
object DomainTools{
  
import scala.math._
import breeze.linalg._  
import breeze.plot._
import scala.annotation.tailrec
import org.jfree.chart.axis.NumberTickUnit

class Rational(num: BigInt, den: BigInt) extends Ordered[Rational] { //Rational number class with arbitrary-precision numerators and denominators
  def abs(n: BigInt): BigInt = if (n >= 0) n else -n
  def gcd(a: BigInt, b: BigInt): BigInt =  
    if (a == 0) abs(b) 
    else if (b == 0) abs(a) 
    else if (abs(a) > abs(b)) gcd(b, abs(a) % abs(b))
    else gcd(a, abs(b) % abs(a))
  val f = gcd(num, den)  //always > 0
  val n = if (den >= 0) num/f else -num/f
  val d = abs(den)/f    //always > 0
  def unary_- =  new Rational(-n,d)
  def recip = new Rational(d, n)
  def + (that: Rational): Rational = new Rational(this.n*that.d+that.n*this.d, this.d*that.d)
  def + (that: Long): Rational = this + new Rational(that, 1)
  def - (that: Rational): Rational = new Rational(this.n*that.d-that.n*this.d, this.d*that.d)
  def - (that: Long): Rational = this - new Rational(that, 1)
  def * (that: Rational): Rational = new Rational(this.n*that.n, this.d*that.d)
  def * (that: Long): Rational = this * new Rational(that, 1)
  def * (that: BigInt): Rational = this * new Rational(that, 1)
  def / (that: Rational): Rational = this*(that.recip)
  def / (that: Long): Rational = this * new Rational(1, that)
  def < (that: Long): Boolean = this < new Rational(that, 1)
  def > (that: Long): Boolean = this > new Rational(that, 1)
  def <= (that: Long): Boolean = this <= new Rational(that, 1)
  def == (that: Rational): Boolean = this.n*that.d == this.d*that.n
  def == (that: Long): Boolean = this == new Rational(that, 1)
  def toReal = n.doubleValue / d.doubleValue
  def toInt = n/d
  def roundDown(bottom: BigInt): Rational = new Rational((n*bottom)/d,bottom)   //largest rational smaller than this having denom dividing bottom
  def roundUp(bottom: BigInt): Rational = new Rational(if (bottom % d == 0) n*(bottom/d) else (n*bottom)/d+1,bottom)
  def compare(that: Rational) = {
    val bigcomp = (this.n)*(that.d)-(this.d)*(that.n)
    if (bigcomp < 0) -1 else if (bigcomp > 0) 1 else 0
  }
  override def toString = if (d == 1) n.toString else n + "/" + d
}

def rationalParse(xs: String): Rational = { //converts user input to Rational
  if (xs.indexOf('.') == -1) {
    val pieces = xs.split('/')
    if (pieces.length < 2) new Rational(pieces(0).toInt,1) else new Rational(pieces(0).toInt,pieces(1).toInt)
  } else {
    val pieces = xs.split('.')
    val decplaces = pieces(1).length()
    new Rational(pieces(0).toInt, 1) + new Rational(pieces(1).toInt, BigInt(10).pow(decplaces))
  }
}

def rsqrt(x: Rational): Rational = { //lower bound for square root of x, with equality if x is a rational perfect square
  def isqrt(n: BigInt): BigInt = { //floor of square root function
    def iter(p: (BigInt, BigInt)): (BigInt, BigInt) = ((p._1 + n/p._1) >> 1,p._1)
    def limit(p: (BigInt, BigInt)): (BigInt, BigInt) = if ((p._1 == p._2) || ((p._1 - p._2).abs ==1 && (p._1*p._1-n)*(p._2*p._2-n)<=0)) p else limit(iter(p))
    val cands = limit((1,n))
    if (cands._2 * cands._2 <= n) cands._2 else cands._1
  }
  val dcand = isqrt(x.d)
  if (dcand * dcand == x.d) new Rational(isqrt(x.n), dcand) else new Rational(isqrt(x.n), dcand + 1)
}

def volhelp(ps: List[(Rational,Rational)]): Rational = ps match { //helper for finding volumes of polygonal domains
      case Nil => new Rational(0,1)
      case _ :: Nil => new Rational(0,1)
      case (a,b) :: (c,d) :: qs => (b-d)*(a+c)/2 + volhelp((c,d) :: qs)
    }

abstract class ToricDomain {
   def ccvWeightSeq: Option[List[Rational]]
   def cvxWeightSeq: Option[(Rational, List[Rational])]
   def volume: Option[Rational] = this match {
     case Ball(c) => Some(c*c/2)
     case Ellipsoid(a, b) => Some(a*b/2)
     case Polydisk(a, b) => Some(a*b)
     case PseudoBall(a, b, c, d) => Some((a*d+b*c)/2)
     case Polygon(pts) => Some(volhelp(pts))                      
     case _ => None
   }
   def maxDual: (Double, Double) => Double = this match {
     case Ball(c) => ((x,y) => Math.max(x*c.toReal, y*c.toReal))
     case Ellipsoid(a, b) => ((x,y) => Math.max(x*a.toReal, y*b.toReal))
     case Polydisk(a,b) => ((x,y) => x*a.toReal + y*b.toReal)
     case PseudoBall(a, b, c, d) => ((x,y) => Math.max(x*c.toReal+y*d.toReal, Math.max(x*a.toReal, y*b.toReal)))
     case Polygon(Nil) => ((x,y) => 0)
     case Polygon((p,q) :: as) => ((x,y) => Math.max(x*p.toReal + y*q.toReal, (new Polygon(as)).maxDual(x,y)))     
   }
   def minDual: (Double, Double) => Double = this match {
     case Ball(c) => ((x,y) => Math.min(x*c.toReal, y*c.toReal))
     case Ellipsoid(a, b) => ((x,y) => Math.min(x*a.toReal, y*b.toReal))
     case Polydisk(a,b) => ((x,y) => Math.min(x*a.toReal, y*b.toReal))
     case PseudoBall(a, b, c, d) => ((x,y) => Math.min(x*c.toReal + y*d.toReal, Math.min(x*a.toReal, y*b.toReal)))
     case Polygon(Nil) => ((x,y) => Double.PositiveInfinity )
     case Polygon((p,q) :: as) => ((x,y) => Math.min(x*p.toReal + y*q.toReal, (new Polygon(as)).minDual(x,y)))     
   }
}

abstract class Target extends ToricDomain {
  def ech: Option[Stream[(Int, Int, Rational)]] = this match {
     case Ellipsoid(a, b) => Some(echgen(a,b))// map (v => v._3) (if I wanted just the capacity, not just m,n)
     case Ball(c) => Some(echgen(c,c))
     case Polydisk(a, b) =>  {
        def incrk(caps: Stream[(Int,Int,Rational)], k: Int): Stream[(Int,Int,Rational)] = {
        lazy val next = caps.filter(v => (v._1+1)*(v._2+1) > k) 
        next.head #:: incrk(next, k+1)
      }      
      Some(incrk(echgen(a,b),0))// map (v => v._3)
     }
     case _ => None 
   }
}

def echgen(a: Rational, b: Rational): Stream[(Int, Int, Rational)] = { //generates the numbers ma+nb in ascending order, remembering m and n
  def extendStream(z: (IndexedSeq[Int], Int)): (IndexedSeq[Int],Int,(Int, Int,Rational)) = z match {
    case (heights, width) => {
      if (heights.isEmpty) (IndexedSeq(0), 0, (0, 0, new Rational(0,1))) else {
        val nextup = IndexedSeq.range(0,width+1) map (i => a*i + b*(heights(i)+1))
	      val upcand = nextup.min
  	    if (nextup.min > a * (width + 1)) (heights :+ 0, width + 1, (width + 1, 0, a*(width+1))) else {
  	     val upind = nextup.indexOf(upcand)
  	     (heights.updated(upind, heights(upind)+1), width, (upind, heights(upind)+1, upcand))
  	    }
	    }
    }
  }
  def advance(y: (IndexedSeq[Int], Int)): Stream[(Int, Int, Rational)] = {
    val z = extendStream(y)
    z._3 #:: advance((z._1, z._2))
  }
  advance((IndexedSeq(), -1))
}

def echbound(source: Target, target: Target, N: Int): Option[(Rational, Int, (Int, Int, Rational), (Int, Int, Rational))] = (source.ech, target.ech) match {
  //when source and target have known ech capacities, gives the best lower bound on dilation of target needed to embed
  //source from the first N ech capacities.  Output is (lower bound, index of optimal capacity, (m,n,capacity) for source, (m,n,capacity) for target)
  case (Some(se), Some(te)) => {
    val slist = (se take N).tail //tail is to avoid getting 0/0 from c0
    val tlist = (te take N).tail
    val ratios = ((slist zip tlist) map (z => z._1._3/z._2._3))
    val best = ratios.max
    val ind = ratios.indexOf(best)
    Some((best, ind + 1, slist(ind), tlist(ind)))
    }
  case _ => None
}

case class DomainBySeq(a: Option[List[Rational]], b: Option[(Rational, List[Rational])]) extends ToricDomain {
  //The point of this class is to avoid re-computing the weight sequences for the types of domains that I'm interested in
  //Of course the volume could be computed from the weight sequences, but isn't needed in the intended uses because it will have already been computed by a simpler formula
  def ccvWeightSeq = a
  def cvxWeightSeq = b
}

case class Ball(val capacity: Rational) extends Target {
  def this(cap: Int) = this(new Rational(cap, 1))
  def ccvWeightSeq = Some(List(capacity))
  def cvxWeightSeq = Some((capacity, List()))
  override def toString = "B(" + capacity + ")"
}

case class Ellipsoid(val a: Rational, val b: Rational) extends Target {
  def this(c: Int, d: Int) = this(new Rational(c,1), new Rational(d,1))
  def this(a: Rational, d: Int) = this(a, new Rational(d,1))
  def this(c: Int, b: Rational) = this(new Rational(c,1), b)
  @tailrec private def ccvacc(h: Rational, w: Rational, acc: List[Rational]): List[Rational] = {
    val m = if (h < w) h else w
    val M = if (w < h) h else w
    if (m == 0) acc else ccvacc(m, M-m, m :: acc)
  }
  def ccvWeightSeq = Some(ccvacc(a, b, Nil))    
  def cvxWeightSeq = {
    val m = if (a < b) a else b
    val M = if (b < a) a else b
    Some((M, ccvacc(M-m, M, Nil)))
  }
  override def toString = "E(" + a + "," + b + ")"
}

case class Polydisk(val a: Rational, val b: Rational) extends Target {
  def this(c: Int, d: Int) = this(new Rational(c,1), new Rational(d,1))
  def this(a: Rational, d: Int) = this(a, new Rational(d,1))
  def this(c: Int, b: Rational) = this(new Rational(c,1), b)
  def ccvWeightSeq = None
  def cvxWeightSeq = Some((a + b, List(a,b)))
  override def toString = "P(" + a + "," + b + ")"
}

case class Polygon(val pts: List[(Rational, Rational)]) extends ToricDomain { //pts should be a list of points in the first quadrant
  //with increasing x coordinate, starting at a point of form (0,b) and ending at a point of form (a,0).
  private def aboveSecant(ends: ((Rational,Rational),(Rational,Rational)), mid: (Rational, Rational)): Boolean = (ends, mid) match {
    case (((x0,y0),(x2,y2)),(x1,y1)) =>  (y2-y0)*(x1-x0) <= (y1-y0)*(x2-x0)
  }
  private def belowSecant(ends: ((Rational,Rational),(Rational,Rational)), mid: (Rational, Rational)): Boolean = (ends, mid) match {
    case (((x0,y0),(x2,y2)),(x1,y1)) =>  (y1-y0)*(x2-x0) <= (y2-y0)*(x1-x0) 
  }
  private val isConvex: Boolean = pts.length < 3 || aboveSecant((pts.head,pts.tail.tail.head),pts.tail.head) && (new Polygon(pts.tail)).isConvex    
  private val isConcave: Boolean = pts.length < 3 || belowSecant((pts.head,pts.tail.tail.head),pts.tail.head) && (new Polygon(pts.tail)).isConcave    
  private def max(qs: List[Rational]): Rational = qs match {
    case Nil => throw new Error("max of empty list")
    case q :: Nil => q
    case q :: ps => { val c = max(ps)
                      if (q > c) q else c}
    }
  private def min(qs: List[Rational]): Rational = qs match {
    case Nil => throw new Error("min of empty list")
    case q :: Nil => q
    case q :: ps => { val c = min(ps)
                      if (q < c) q else c}
    }
  def cvxWeightSeq = if (!isConvex) None else {
    val container = max(pts map (x => x._1 + x._2))
    val tangent = pts filter (x => x._1 + x._2 == container)
    val leftOut = pts filter (x => x._1 <= tangent.head._1)
    val rightOut = pts filter (x => tangent.last._1 <= x._1)
    val leftMoved = leftOut map (x => (container - x._1 -x._2, x._1))
    val rightMoved = rightOut map (x => (x._2, container - x._1 - x._2))
    Some(container, (new Polygon(leftMoved)).ccvWeightSeq.get ++ (new Polygon(rightMoved)).ccvWeightSeq.get)
  }
  def ccvWeightSeq = if (!isConcave) None else if (pts.length <= 1) Some(List()) else {
    val inscribed = min(pts map (x => x._1 + x._2))
    val tangent  = pts filter (x => x._1 + x._2 == inscribed)
    val leftHalf = pts filter (x => x._1 <= tangent.head._1)
    val rightHalf = pts filter (x => tangent.last._1 <= x._1)
    val leftMoved = leftHalf map (x => (x._1, x._1+x._2-inscribed))
    val rightMoved = rightHalf map (x => (x._1 + x._2 - inscribed, x._2))
    if (inscribed == 0) Some(List()) else 
      Some(inscribed :: (new Polygon(leftMoved)).ccvWeightSeq.get ++ (new Polygon(rightMoved)).ccvWeightSeq.get)   
  }
}


case class PseudoBall(val a: Rational, val b: Rational, val c: Rational, val d: Rational) extends ToricDomain {
  // convex domain with vertices (0,b), (c,d), (a,0).  Assume c+d>=b>=a
  def ccvWeightSeq = None
  def cvxWeightSeq = Some((c+d, (new Ellipsoid(c+d-b,c)).ccvWeightSeq.get ++ (new Ellipsoid(c+d-a,d)).ccvWeightSeq.get))
  override def toString = "T(" + a + "," + b + "," + c + "," + "d)"
}

def scale(dom: ToricDomain, lambda: Rational): ToricDomain = {
  val t = dom.ccvWeightSeq
  val a = if (t.isDefined) Some(t.get map (x => lambda * x)) else None
  val u = dom.cvxWeightSeq
  val b = if (u.isDefined) Some((lambda * (u.get)._1 , (u.get)._2 map (x => lambda * x))) else None 
  DomainBySeq(a,b)
}
  
def embed(source: ToricDomain, target: ToricDomain): Boolean = (source.ccvWeightSeq, target.cvxWeightSeq) match {
  //true iff source symplectically embeds in arbitrarily small dilates of target
  case (None, _) => throw new Error("Domain is not concave")
  case (_, None) => throw new Error("Target is not convex")
  case (Some(as),Some((h,ds))) => (new SympClass(h, (as ++ ds).sortWith(_ > _))).inConeClosure 
}

class SympClass(val hyp: Rational, val divs: List[Rational]) { //represent a class as (hyp)H-sum(divs)_iE_i where divs is sorted in descending order
  //the method inConeClosure says whether this class is in the closure of the symplectic cone (which is equivalent to 
  //solving the ball-packing problem for balls of capacities divs into arbitrarily small dilates of a ball of capacity hyp
  def negCoeff: Boolean = !((hyp :: divs) filter (x => x < 0)).isEmpty
  def negSquare: Boolean = hyp*hyp < (divs map (x => x*x) reduceLeft(_+_))
  val delta: Rational = divs match {
    case d1 :: d2 :: d3 :: ds => d1 + d2 + d3 - hyp
    case _ => (new SympClass(hyp,divs ++ List(new Rational(0,1),new Rational(0,1),new Rational(0,1)))).delta
  }
  @tailrec private def insertHelp(x: Rational, pref: List[Rational], suff: List[Rational]): List[Rational] = suff match {
      case Nil => pref ++ List(x)
      case y :: ys => if (x < y) insertHelp(x, pref ++ List(y), ys) else pref ++ List(x) ++ suff
    }
  def insert(x: Rational, ds: List[Rational]): List[Rational] = insertHelp(x, Nil, ds)
  def cremona: SympClass = divs match {
    case d1 :: d2 :: d3 :: ds => if (delta <= 0) this else new SympClass(hyp - delta, insert(d1-delta,insert(d2-delta,insert(d3 - delta,ds))))
    case _ => (new SympClass(hyp,divs ++ List(new Rational(0,1),new Rational(0,1),new Rational(0,1)))).cremona
  }
  def reduce(cls: SympClass): SympClass = 
    if (cls.negCoeff || cls.delta <= 0) cls else reduce(cls.cremona)
  def inConeClosure: Boolean = (!negSquare) && (!reduce(this).negCoeff)
}

val half = new Rational(1,2)

def optEllipseToConvexDomain(a: Rational, D: ToricDomain, N: BigInt, seed: (Rational, Rational) = (new Rational(0,1), new Rational(10,1))): (Rational, Rational) = {
//Uses bisection to determine a width-1/N interval containing the infimal lambda such that E(1,a) embeds into lambdaD
  val tol = new Rational(1, N)
  val seq = D.cvxWeightSeq.get
  val source = new DomainBySeq(Some((new Ellipsoid(new Rational(1,1),a)).ccvWeightSeq.get), None)
  val target = new DomainBySeq(None, Some(seq))
  def shrink(interval: (Rational, Rational)): (Rational, Rational) = {
    val lo = interval._1
    val hi = interval._2
    val mid = half * (lo + hi)
    if (embed(source, scale(target, mid))) (lo.roundDown(N), mid.roundUp(N)) else (mid.roundDown(N), hi.roundUp(N))
  }
  def repShrink(interval: (Rational, Rational)): (Rational, Rational) = {
    if (interval._2 - interval._1 <= tol) interval else repShrink(shrink(interval))
  }
  repShrink(seed) //Assumes needed dilation factor is in [0,10]. Could try implementing something giving better bounds on the initial interval
  }


def listOptCvx(xs: List[Rational], D: ToricDomain, N: BigInt): List[Rational] =  {
  //helper for getting a long list of values embed(a,D,N) as a varies
  @tailrec def listacc(acc: List[Rational], qs: List[Rational], seed: (Rational, Rational)): List[Rational] = qs match {
    case Nil => acc 
    case q :: Nil => acc ++ List(optEllipseToConvexDomain(q, D, N, seed)._2)
    case q :: p :: ps => { val y = optEllipseToConvexDomain(q, D, N, seed)._2
                           listacc(acc ++ List(y), p :: ps, (y-new Rational(2,N),y*p/q + new Rational(2,N))) }
  }
  listacc(Nil, xs, (new Rational(0,1), new Rational(10,1)))    
  }

def bgraph(a: Rational, xDensity: BigInt = 1000, accuracy: BigInt = 1000): Unit = {
  //plots c_b(a)=inf{d|E(1,a)->dP(1,b)} as a function of *b* with a fixed.
  val rs = (xDensity to xDensity*2) map (b => new Rational(b,xDensity))
  val xs = rs map (b => b.toReal)
  val ys = rs map (b =>  optEllipseToConvexDomain(a, new Polydisk(1,b), accuracy)._2.toReal/sqrt(a.toReal/(2*b.toReal)))
  val zs = xs map (b => sqrt( a.toReal/(2*b)))
  val f = Figure("a = " + a +", b\u2208 [1,2]")
  val p = f.subplot(0)  
  p += plot(DenseVector(xs.toArray), DenseVector(ys.toArray), name = "Scaling required to embed E(1," + a + ") into P(1,b)")
  p += plot(DenseVector(xs.toArray), DenseVector(zs.toArray), name = "Volume bound") 
  p.xaxis.setTickUnit(new NumberTickUnit(0.1))
  p.yaxis.setTickUnit(new NumberTickUnit(0.05))
  p.xlabel = "b"
  p.legend = true
  f.refresh()
}


def convexGraph(D: ToricDomain,  xmin: Rational, xmax: Rational, xDensity: BigInt = 1000, accuracy: BigInt = 1000): Figure = {
  //plots a\mapsto inf\{d|E(1,a)->dD as a function of a.  D should be a convex toric domain.
  val rs = ((xmin * xDensity).toInt to (xmax*xDensity).toInt) map (a => new Rational(a,xDensity))
  val xs = rs map (a => a.toReal)
  val ys = listOptCvx(rs.toList, D, accuracy) map (a => a.toReal)
  val zs = if (D.volume.isDefined) xs map (a => sqrt(a / (2*D.volume.get.toReal))) else List()  //volume bound if optional volume parameter (of the unrescaled target) is supplied
  val f = Figure(D.toString + "  (a\u2208[" + xmin.toString + ", " + xmax.toString + "])")
  val p = f.subplot(0)
  p += plot(DenseVector(xs.toArray), DenseVector(ys.toArray), name = "Scaling required to embed E(1,a) into " + D.toString) 
  if (D.volume.isDefined) p += plot(DenseVector(xs.toArray), DenseVector(zs.toArray), name = "Volume bound") 
  p.xaxis.setTickUnit(new NumberTickUnit((xmax.toReal-xmin.toReal)*0.1))
  p.yaxis.setTickUnit(new NumberTickUnit((ys.last - ys.head)*0.1))
  p.xlabel = "a"
  p.legend = true
  f
}


def optConcaveDomainToEllipse(D: ToricDomain, a: Rational, N: Long, seed: (Rational, Rational) = (new Rational(0,1), new Rational(10,1))): Rational = {
  //this method and the two following are analogues of ones above but for mapping concave domains to ellipsoids instead of ellipsoids to convex domains
  val tol = new Rational(1, N)
  val seq = D.ccvWeightSeq.get
  val target = new DomainBySeq(None, Some((new Ellipsoid(new Rational(1,1),a)).cvxWeightSeq.get))
  val source = new DomainBySeq(Some(seq), None)
    def shrink(interval: (Rational, Rational)): (Rational, Rational) = {
    val lo = interval._1
    val hi = interval._2
    val mid = half * (lo + hi)
    if (embed(scale(source, mid), target)) (mid.roundDown(N), hi.roundUp(N)) else (lo.roundDown(N), mid.roundUp(N))
  }
  def repShrink(interval: (Rational, Rational)): (Rational, Rational) = {
    if (interval._2 - interval._1 <= tol) interval else repShrink(shrink(interval))
  }
  val finalInt = repShrink(seed) //Assumes needed dilation factor is in [0,10]. Could try implementing something giving better bounds on the initial interval
  finalInt._2
}

def listOptCcv(xs: List[Rational], D: ToricDomain, N: Int): List[Rational] =  {
  @tailrec def listacc(acc: List[Rational], qs: List[Rational], seed: (Rational, Rational)): List[Rational] = qs match {
    case Nil => acc 
    case q :: Nil => acc ++ List(optConcaveDomainToEllipse(D, q, N, seed))
    case q :: p :: ps => { val y = optConcaveDomainToEllipse(D, q, N, seed)
                           listacc(acc ++ List(y), p :: ps, (y-new Rational(2,N),y*p/q + new Rational(2,N))) }
  }
  listacc(Nil, xs, (new Rational(0,1), new Rational(10,1)))    
  }

def concaveGraph(D: ToricDomain, xmin: Rational, xmax: Rational, xDensity: Int = 1000, accuracy: Int = 1000): Unit = {
  val rs = ((xmin*xDensity).toInt to (xmax*xDensity).toInt) map (a => new Rational(a,xDensity))
  val xs = rs map (a => a.toReal)
  val ys = listOptCcv(rs.toList, D, accuracy) map (a => a.toReal)
  val zs = if (D.volume.isDefined) xs map (a => sqrt(a/(2*D.volume.get.toReal))) else List()  //volume bound if optional volume parameter (of the unrescaled target) is supplied
  val dells = xs.zip(ys) map (p => 1/(D.minDual(p._2,p._2/p._1)))
  val dellubound = xs map (_ => Math.min(D.minDual(1,2), D.minDual(2,1))/D.minDual(1,1))
  val f = Figure()
  val p = f.subplot(0)
  p += plot(DenseVector(xs.toArray), DenseVector(ys.toArray))
  p += plot(DenseVector(xs.toArray), DenseVector(dells.toArray))
  p += plot(DenseVector(xs.toArray), DenseVector(dellubound.toArray))
  if (D.volume.isDefined) p += plot(DenseVector(xs.toArray), DenseVector(zs.toArray))
  f.saveas("ccv.eps")
}

def volFills( NB: Int, NC: Int): Unit = { 
  //Searches for and plots points (a,b) such that E(1,a) fully fills a dilate of P(1,b).  NB is the search density for b, and NC is the search density for the dilation factor.
  def tester(numB: Int, numC: Int): Boolean = {
    val b = new Rational(numB, NB)
    val c = new Rational(numC, NC)
    val a = c*c*b*2
    embed(new Ellipsoid(new Rational(1,1), a), new Polydisk(c, c*b))
  }
  val full = for { b0 <- (NB to 2*NB)
                  c0 <- (NC to 3*NC)
                  if c0*c0*b0*2 < 10*NC*NC*NB &&  tester(b0, c0)
  }  
  yield (((new Rational(c0, NC))*(new Rational(c0, NC))*(new Rational(b0, NB))*2).toReal, (new Rational(b0,1)).toReal)
  val f = Figure()
  val p = f.subplot(0)
  val as = full map (_._1)
  val bs = full map (_._2)
  p += plot(DenseVector(as.toArray), DenseVector(bs.toArray),'.')
  f.saveas("volfills.eps")
}

def threeLargestInds(xs: IndexedSeq[Rational]): (Int, Int, Int) = {
  //helper for doing Cremona moves in place without sorting (which is better for finding exceptional sphere obstructions)
	val zipped = xs.zipWithIndex
	def largestPair(ys: IndexedSeq[(Rational, Int)]): (Rational, Int) = ys.maxBy(p => p._1)
	val first = largestPair(zipped)
	val delOne = zipped diff List(first)
	val second = largestPair(delOne)
	val delTwo = delOne diff List(second)
	(first._2, second._2, largestPair(delTwo)._2)
}            

def cremMove(xs: IndexedSeq[Rational], inds: (Int, Int, Int)): IndexedSeq[Rational] = {
	val delta = xs(0) - xs(inds._1+1) - xs(inds._2+1) - xs(inds._3+1)
	xs.updated(0, xs(0) + delta).updated(inds._1+1, xs(inds._1+1) + delta).updated(inds._2+1, xs(inds._2+1) + delta).updated(inds._3+1, xs(inds._3+1)+delta)}

def reduceInPlace(cs: IndexedSeq[Rational], strict: Boolean): (IndexedSeq[Rational], List[(Int, Int, Int)]) = {
  //Applies successive Cremona moves to cs until cs is reduced or has a negative/nonpositive (depending on strict) entry.  Second item in output is a list of the Cremona moves applied, in reverse order
	 val negcrit: (Rational => Boolean) = if (strict) (q => q < new Rational(0,1)) else (q => q <= new Rational(0,1))
  @tailrec def reduceInPlaceHelper(t: (IndexedSeq[Rational], List[(Int, Int, Int)])): (IndexedSeq[Rational], List[(Int, Int, Int)]) = t match {
  	case (xs, moves) => {
  		if (xs.exists(negcrit)) (xs, moves) else {
				val inds = threeLargestInds(xs.tail)
				if (xs(0) >= xs(inds._1+1) + xs(inds._2+1) + xs(inds._3+1)) (xs, moves) else
				  reduceInPlaceHelper((cremMove(xs, inds), inds :: moves))
			}
		}
	}
	cs.length match {
	  case len if len < 3 => (cs, Nil)
	  case len if len == 3 => {
	    val delta = cs(0)-cs(1)-cs(2)
	    if (delta > 0) (cs, Nil) else (IndexedSeq(cs(0)+delta,cs(1)+delta,cs(2)+delta,delta),List((0,1,2)))
	  }
	  case _ => reduceInPlaceHelper((cs, Nil))
	}
}     

def cremSeq(c: IndexedSeq[Rational], moves: List[(Int, Int, Int)]): IndexedSeq[Rational] = moves match {
  //Applies a list of Cremona moves, in order, to the class c
	case Nil => c
  case m :: ms => cremSeq(cremMove(c, m), ms)
  }                                               

def findObstruction(coh: IndexedSeq[Rational], strict: Boolean): Option[IndexedSeq[Rational]] = {
  //Finds the class of an exceptional sphere with which coh (expressed in terms of the basis (H,-E_1,...,-E_k) for a blowup of CP2)
  //pairs negatively if strict is set to true or nonpositively if strict is set to false. The method applies Cremona moves to coh until it has a negative 
  //or nonpositive entry in some position i, and then applies  the same Cremona moves in reverse order to E_i
	val reduction = reduceInPlace(coh, strict)
	val neg = if (strict) reduction._1.zipWithIndex.find(p => (p._2 > 0 && p._1 < new Rational(0,1))) else
	            reduction._1.zipWithIndex.find(p => (p._2 > 0 && p._1 <= new Rational(0,1)))
	neg match {
		case None => None
		case Some(p) => {
			val exc = (reduction._1 map (x => new Rational(0,1))).updated(neg.get._2, new Rational(-1,1))
			Some(cremSeq(exc, reduction._2))
		}
	}
}                                                 

def obstruct(D: ToricDomain, T: Target, dil: Rational, strict: Boolean): Option[IndexedSeq[Rational]] = T match {
  //Gives exceptional sphere obstruction to embedding E into the interior of dil*P.  Output is expressed in terms of homology of blowups
  //of S2xS2 as in Frenkel-Muller (first two entries are fiber and section classes, rest are negative exceptional divisors)
  case Ellipsoid(c, d) => {
    val epsilon = new Rational(1,1) - new Rational(1, BigInt(1837818000) * 10000)
    val targetSeq = if (strict) (T.cvxWeightSeq.get._1 :: T.cvxWeightSeq.get._2.reverse).toIndexedSeq else
      (T.cvxWeightSeq.get._1 :: (T.cvxWeightSeq.get._2.reverse map (x => x * epsilon))).toIndexedSeq
      //the right condition for a non-strict obstruction is that (head, w(D), a\hat{w}(T)).E for all a<1, which is why I use epsilon here.  
      //This does potentially cause one to miss close-to-volume obstructions  for embeddings into some ellipsoids
    val sourceSeq = D.ccvWeightSeq.get
    findObstruction(IndexedSeq((targetSeq.head)*dil) ++ sourceSeq.reverse.toIndexedSeq ++ (targetSeq.tail map (a => a*dil)), strict)
    }
  case Polydisk(c, d) => {
    val domseq = D.ccvWeightSeq.get.reverse
    val cp2class = findObstruction(IndexedSeq(dil*(c + d) - domseq.head, dil*d - domseq.head, dil*c - domseq.head) ++ domseq.tail.toIndexedSeq, strict)
    cp2class match {
   	case None => None
   	case Some(v) => {
     		val h = v(0)  //This changes basis from blowups of CP2 to blowups of S2xS2
     		val m1 = v(1)
     		val m2 = v(2)
     		Some(IndexedSeq(h-m2, h-m1, h-m1-m2) ++ (v drop 3))
		}
    }
	}
}

def dot(x: IndexedSeq[Rational], y: IndexedSeq[Rational]): Rational = ((x zip y) map ({ case (q, r) => q * r})).foldLeft(new Rational(0,1)) (_+_)
//dot product (with shorter vector padded by zeros)


def minscale(D: ToricDomain, T: Target, E: IndexedSeq[Rational]): Rational = T match {
  case Polydisk(c, d) => dot(D.ccvWeightSeq.get.reverse.toIndexedSeq, E drop 2) / (c*E(0) + d*E(1))
  case Ellipsoid(_,_) => {
    val tdata = T.cvxWeightSeq.get
    val ddata = D.ccvWeightSeq.get
    val break = ddata.length
    val denom = tdata._1 * E(0) - dot(tdata._2.reverse.toIndexedSeq, E.tail drop break)
    if (denom == new Rational(0,1)) new Rational(-1,1) else
      dot(D.ccvWeightSeq.get.reverse.toIndexedSeq, E.tail take break) /  denom  
    }
}
  
def nextSphere(D: ToricDomain, T: Target, E: IndexedSeq[Rational]): Option[IndexedSeq[Rational]] = {
  val nextscale = minscale(D, T, E)
  if (nextscale == new Rational(-1,1)) None else obstruct(D, T, minscale(D, T, E), true)
}
  
def dilateViaExcSpheres(a: Rational, T: Target, N: BigInt): (Rational, Option[IndexedSeq[Rational]]) = {
  val D = new Ellipsoid(1, a)
  val volbound = rsqrt(D.volume.get / T.volume.get)
  if (embed(D, scale(T, volbound))) (volbound, None) else {
    val interval = optEllipseToConvexDomain(a, T, N, (volbound, volbound * 8))
    @tailrec def dilateacc(sphere: IndexedSeq[Rational]): IndexedSeq[Rational] = nextSphere(D, T, sphere) match {
      case None => sphere
      case Some(s) => dilateacc(s)
    }
    if (interval._1 * interval._1 * (T.volume.get) < D.volume.get) (interval._2, None) else {
      val initSphere = obstruct(D, T, interval._1, false)
      if (!initSphere.isDefined) (interval._2, None) else {
        val bestobs = dilateacc(initSphere.get)
        (minscale(D, T, bestobs), Some(bestobs))
      }
    }
  }
}
//def main(args: Array[String]): Unit = {
  //volFills(30,60)
//}
  


}





