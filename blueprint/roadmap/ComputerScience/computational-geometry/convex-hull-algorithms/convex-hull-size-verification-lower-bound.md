# Lower bound for convex hull size verification

Fix $d \ge 1$. In the *convex hull size verification* problem the input is a list of $n$ points $p_1, \dots, p_n$ of $\mathbb{R}^2$, given by their $2n$ coordinates and not necessarily distinct, together with an integer $h$, and the answer is yes when $\operatorname{conv}\{p_1, \dots, p_n\}$ has exactly $h$ distinct vertices. There are constants $c_d > 0$ and $h_d \ge 3$, depending only on $d$, such that for all $n \ge h \ge h_d$ every $d$-th order algebraic decision tree that decides, for these $n$ and $h$, the set of yes-inputs in $\mathbb{R}^{2n}$ has height at least $c_d \, n \log_2 h$. Hence computing the vertices of the convex hull of $n$ points with $h$ hull vertices takes $\Omega(n \log h)$ time in this model, and $\Omega(n \log n)$ in the worst case.

## Depends on

- [Convex hull of a finite planar point set](convex-hull-of-a-finite-planar-point-set.md)
- [Algebraic decision tree](algebraic-decision-tree.md)

## Proof depends on

- [Lower bound for multiset size verification](multiset-size-verification-lower-bound.md)
- [Sorting reduces to the planar convex hull problem](sorting-reduces-to-the-planar-convex-hull-problem.md)

## Sources

- D. G. Kirkpatrick and R. Seidel, "The ultimate planar convex hull algorithm?", *SIAM Journal on Computing* 15(1) (1986), 287–299, <https://doi.org/10.1137/0215021>: Section 5, Theorem 5.2 (convex hull size verification needs $\Omega(n \log H)$ steps on $d$-th order algebraic decision trees), by the reduction $p_i = (z_i, z_i^2)$ from Corollary 5.1
- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 3, the theorem that the CHSV problem requires $\Omega(n \log h)$ time, by lifting a multiset size verification instance to the parabola
