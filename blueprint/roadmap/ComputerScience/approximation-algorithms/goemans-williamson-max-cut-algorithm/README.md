# Goemans–Williamson MAX-CUT algorithm

Goemans and Williamson (*J. ACM* 42(6) (1995)) relax MAX CUT, the problem of maximizing
$\frac12 \sum_{i<j} w_{ij}(1 - y_i y_j)$ over $y \in \{-1, 1\}^V$, to the vector program (P) that
maximizes $\frac12 \sum_{i<j} w_{ij}(1 - v_i \cdot v_j)$ over unit vectors $v_i$, a semidefinite program.
They round an optimal solution by a random hyperplane through the origin: $i \in S$ when
$v_i \cdot r \ge 0$. A hyperplane separates $v_i$ and $v_j$ with probability
$\arccos(v_i \cdot v_j)/\pi$ (Lemma 3.2), so the expected cut weight is
$\sum_{i<j} w_{ij} \arccos(v_i \cdot v_j)/\pi$ (Theorem 3.1). For nonnegative weights, comparing this term by
term with the objective of (P) (Lemma 3.4) gives an expected cut of at least $\alpha$ times the
relaxation value, hence at least $\alpha \cdot \mathrm{OPT}$, with
$\alpha = \min_{0<\theta\le\pi} \frac{2}{\pi} \frac{\theta}{1-\cos\theta} > 0.87856$ (Theorem 3.3, Lemma 3.5).

The results below take the direction $r$ to be a standard Gaussian vector (which, as the paper
notes, gives the same cut as a uniform point on the sphere): the relaxation property ($Z_P \ge$
every cut), Lemma 3.2, Theorem 3.1, the constant $\alpha$ with Lemma 3.4 and a certified bound for
Lemma 3.5, and Theorem 3.3, hence the guarantee $\mathbb{E}[w(S, \bar S)] \ge \alpha \cdot \mathrm{OPT}$
for vectors attaining $Z_P$. Moreover (P) and its semidefinite form,
$\max \frac12\sum_{i<j} w_{ij}(1 - Y_{ij})$ over positive semidefinite $Y$ with unit diagonal, have
the same feasible values when vectors of any dimension are allowed (Gram matrices). For integral weights,
the paper also solves the semidefinite program to any accuracy $\varepsilon > 0$ in time
polynomial in the input size and $\log(1/\varepsilon)$, and it extends the method to MAX 2SAT and
MAX DICUT (§7).

## The relaxation

- [Ordered pairs of vertices](pairs.md)
- [Objective of the MAX CUT quadratic program](quad-objective.md)
- [Weight of a cut](cut-weight.md)
- [Sign vector of a cut](cut-sign.md)
- [The quadratic program computes cut weights](quad-objective-cut-sign.md)
- [Objective of the vector relaxation](vector-objective.md)
- [Value of the vector relaxation](relaxation-value.md)
- [The relaxation objective is bounded on unit vectors](vector-objective-le-sum-abs.md)
- [The relaxation objective is nonnegative for nonnegative weights](vector-objective-nonneg.md)
- [Cuts embed in the vector relaxation](vector-objective-cut-sign-single.md)
- [The vector relaxation bounds every cut](cut-weight-le-relaxation-value.md)

## The semidefinite program

- [Objective of the MAX CUT semidefinite program](sdp-objective.md)
- [Feasible matrices of the MAX CUT semidefinite program](sdpfeasible.md)
- [Unit vectors give feasible matrices](sdp-feasible-gram.md)
- [Feasible matrices are Gram matrices of unit vectors](exists-gram-eq-of-sdp-feasible.md)

## The constant

- [The Goemans–Williamson constant](gw-constant.md)
- [The Goemans–Williamson constant is a lower bound for the ratio](gw-constant-le.md)
- [Goemans–Williamson Lemma 3.4, angle form](gw-constant-mul-le.md)
- [Goemans–Williamson Lemma 3.4](gw-constant-mul-le-arccos-div-pi.md)
- [The Goemans–Williamson inequality with a certified constant](certified-mul-one-sub-cos-le.md)
- [Goemans–Williamson Lemma 3.5](lt-gw-constant.md)
- [The Goemans–Williamson constant is at most one](gw-constant-le-one.md)

## Random-hyperplane rounding

- [Goemans–Williamson Lemma 3.2: probability that a random hyperplane separates two unit vectors](measure-real-sign-ne.md)
- [Expected weight of the random-hyperplane cut](hyperplane-expectation.md)
- [Goemans–Williamson Theorem 3.1: expected weight of the random-hyperplane cut](integral-cut-weight-hyperplane.md)
- [Goemans–Williamson Theorem 3.3, term-by-term comparison](gw-constant-mul-vector-objective-le.md)
- [Goemans–Williamson Theorem 3.3 with the numerical constant](mul-vector-objective-le-hyperplane-expec.md)
- [Goemans–Williamson Theorem 3.3](gw-constant-mul-vector-objective-le-inte.md)
- [The Goemans–Williamson guarantee](gw-constant-mul-cut-weight-le-integral.md)
- [The Goemans–Williamson guarantee for nearly optimal vectors](gw-constant-mul-cut-weight-sub-le-integr.md)

## Simpler MAX-CUT guarantees

- [MAX-CUT: the random cut and local search](max-cut-the-random-cut-and-local-search/README.md): in an unweighted graph a uniformly random cut cuts half of the edges in expectation and a locally optimal cut cuts at least half, the guarantees the semidefinite rounding improves on

## Related topics

- [Theta function of a graph](../../../GraphTheory/graph-invariants-and-labelings/theta-function-of-a-graph/README.md): the
  Lovász theta function is the first semidefinite relaxation of a combinatorial problem; the
  MAX CUT relaxation is built the same way, from vectors attached to vertices (Goemans,
  *Math. Programming* 79 (1997), §3 and §5).
- [Ellipsoid method](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/README.md): the
  Grötschel–Lovász–Schrijver route to solving semidefinite programs, and hence (P) for integral
  weights, to any accuracy $\varepsilon > 0$ in time polynomial in the input size and
  $\log(1/\varepsilon)$.
- [Lagrange duality](../../../Analysis/convex-analysis-and-variations/lagrange-duality/README.md): the
  dual of (P) is the eigenvalue bound of Delorme and Poljak (survey §5).
- [Maximum cut](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/maximum-cut/README.md):
  NP-completeness of the problem being approximated.
- [Inapproximability of MAX-CUT](../../../TheoryOfComputation/pcp-and-inapproximability/inapproximability-of-max-cut/README.md):
  the hardness side: MAX-CUT has no polynomial-time approximation scheme unless P = NP. Stronger
  hardness results are Håstad's $16/17$ bound and, under the Unique Games Conjecture, the
  optimality of $\alpha$.
- [Randomized rounding for MAX-SAT](../randomized-rounding-for-max-sat/README.md): the
  linear-programming predecessor of the same rounding philosophy, by the same authors.
