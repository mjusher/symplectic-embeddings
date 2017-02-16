import scala.swing._
import scala.swing.event._
import java.awt.Color
import breeze.plot._
import DomainTools._

class SEEP extends MainFrame {
  val err = new Label("")
  err.foreground = Color.RED
  val dilout = new Label("Finds optimal embedding by searching for a sharp exceptional sphere obstruction")
  val fillout = new Label("or (when the box above is checked) a sharp ECH capacity bound.")
  val capout = new Label("Otherwise, dilation factor will be accurate to within 1/180,000,000")
  val obsout = new Label("")
  title = "Symplectic embeddings of ellipsoids"
  val dims = new TextField(3)
  val mina = new TextField(3)
  val maxa = new TextField(3)
  val onea = new TextField(4)
  val echk = new TextField(3)
  val ell = new RadioButton("Ellipsoid")
  val pol = new RadioButton("Polydisk")
  val domtype = new ButtonGroup(ell, pol)
  val prec = new ComboBox(List(1,2,3,5,10))
  val echChoose = new ComboBox(List(200, 500, 1000, 2000, 5000))
  val saveBox = new CheckBox("save?")
  val echBox = new CheckBox("Compute ECH capacities?")
  contents = new BoxPanel(Orientation.Vertical) {
  contents += new BoxPanel(Orientation.Horizontal) {
    contents += new BoxPanel(Orientation.Vertical) {
      contents += new Label("Target type")
      contents += Swing.VStrut(5)
      contents += ell
      contents += pol  
    }
    contents += Swing.HStrut(30)
    contents += new BoxPanel(Orientation.Vertical) {
      contents += new BoxPanel(Orientation.Vertical) {
        contents += new Label("Aspect ratio of target (i.e. c such that target = E(1,c) or P(1,c))")
        contents += new Label("(input can be formatted as integer, decimal, or fraction like 289/36)")
      }
      contents += new BoxPanel(Orientation.Vertical) {
      contents += dims
      contents += Swing.VStrut(10)
      }
    }
    contents += Swing.HStrut(300) 
  }
    contents += Swing.VStrut(10)
    contents += new BoxPanel(Orientation.Horizontal) {
     contents += new BoxPanel(Orientation.Vertical) {
      contents += new BoxPanel(Orientation.Horizontal) {
        contents += new BoxPanel(Orientation.Vertical) {
           contents += new Label("Embed E(1,a) into target for this range of a:  ")
        }
        contents += new BoxPanel(Orientation.Horizontal) {
          contents += mina
          contents += new Label(" to ")
          contents += maxa
        }
      }
      contents += Swing.VStrut(10)
      contents += new BoxPanel(Orientation.Horizontal) {
        contents += new Label("Precision (higher is slower)  ")
        contents += prec
      }
      contents += Swing.VStrut(10)
      contents += Button("Plot staircase graph") { staircase() }
      contents += saveBox
      contents += Swing.VStrut(5)
      contents += err
        border = Swing.BeveledBorder(Swing.Lowered)

     }
     contents += new BoxPanel(Orientation.Vertical) {
       contents += new BoxPanel(Orientation.Horizontal) {
         contents += new BoxPanel(Orientation.Vertical) {
           contents += new Label("Find the smallest dilate of the target admitting")
           contents += new Label("an embedding of E(1,a) for this specific a:")
           }
         contents += new BoxPanel(Orientation.Vertical) {
           contents += Swing.VStrut(25)
           contents += onea
           contents += Swing.VStrut(25)
           }
         contents += new BoxPanel(Orientation.Vertical) {
           contents += echBox
           contents += new BoxPanel(Orientation.Horizontal) {
             contents += new Label("How many?")
             contents += echChoose
             }
           }
         contents += Swing.HStrut(25)

     }
     contents += Button("Calculate optimal embedding") { dilate() }
     contents += dilout
     contents += fillout
     contents += capout
     contents += obsout
       border = Swing.BeveledBorder(Swing.Lowered)

     }
    }
    contents += Swing.VStrut(5)  
    contents += Button("Close") {closeMe()}
    contents += Swing.VStrut(15)
    border = Swing.EmptyBorder(10,10,10,10)
  }
  
  def staircase() {
    if (!ell.selected && !pol.selected) err.text = "Select ellipsoid or polydisk" else {
      val dom = if (ell.selected) new Ellipsoid(1, rationalParse(dims.text)) else new Polydisk(1, rationalParse(dims.text))
      val left = rationalParse(mina.text)
      val right = rationalParse(maxa.text)
      if (right <= left) err.text = "Error: endpoints in wrong order" else {
        err.text = ""
        val fineness = (prec.selection.item) * ((new Rational(800,1)) / (right-left)).toInt.intValue()
        val graph = convexGraph(dom, left, right, fineness, fineness)
        graph.refresh()
        if (saveBox.selected) {
          graph.saveas("graph.eps")        
        }
      }
    }
  }
  
  def dilate() {
      if (!ell.selected && !pol.selected) err.text = "Select ellipsoid or polydisk" else {
        val target: Target = if (ell.selected) new Ellipsoid(1, rationalParse(dims.text)) else new Polydisk(1, rationalParse(dims.text))
        val aspect = rationalParse(onea.text)
        val source = new Ellipsoid(1, aspect)
        val ebound = if (echBox.selected) echbound(source, target, echChoose.selection.item) else None
        val echgood = ebound match {
          case None => false
          case Some((lambda, _,_,_)) => embed(source, scale(target, lambda))
        }
        val d: (Rational, Option[IndexedSeq[Rational]]) = dilateViaExcSpheres(aspect, target, 183781800)
        val scaledTarget = if (ell.selected) new Ellipsoid(d._1,d._1 * rationalParse(dims.text)) else new Polydisk(d._1,d._1 * rationalParse(dims.text))
        val filled = aspect.toReal / (2*scaledTarget.volume.get.toReal)
        val filltext = if (aspect == scaledTarget.volume.get * 2) "Full filling.  " else "%.8f".format(filled) + " of volume filled.  "
        val echtext = if (echgood) "Sharp by ECH capacity " + ebound.get._2 + "." else ""
        dilout.text = "E(1," + aspect + ") \u21AA " + scaledTarget.toString + ".  " 
        dilout.foreground = Color.BLUE
        fillout.text = filltext + echtext
        capout.text = if (echgood) {
          val sech = source.ech.get(ebound.get._2)
          val tech = target.ech.get(ebound.get._2)
          sech._3 + " = " + sech._1 + "+" + sech._2 + "*" + aspect + " vs. " + tech._3 + " = " + tech._1 + "+" + tech._2 + "*" + rationalParse(dims.text) 
        } else ""
        obsout.text = if (!d._2.isDefined) "" else {
            val out = d._2.get filter (x => x > new Rational(0,1))
            if (ell.selected) 
               "Exceptional sphere obstruction:  (" + out(0) + ";  " + out.tail.mkString(", ") + ")"  else {
                "Exceptional sphere obstruction: (" + out(0) + ", " + out(1) + ";  " + out.tail.tail.mkString(", ") + ")"
            }
          }
      }
  }

  def closeMe() {
    val res = Dialog.showConfirmation(contents.head, "Do you want to quit?", optionType=Dialog.Options.YesNo, title=title)
    if (res == Dialog.Result.Ok) sys.exit(0)
  }
}

object SEEP {
  def main(args: Array[String]): Unit = {
    val ui = new SEEP
    ui.visible = true
  }
}