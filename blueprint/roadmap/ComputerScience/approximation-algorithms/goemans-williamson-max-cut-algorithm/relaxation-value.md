# Value of the vector relaxation

The supremum $Z_P$ of the [relaxation objective](vector-objective.md) over families of unit
vectors $v_i \in \mathbb{R}^m$, taken to be $0$ when there is no such family ($m = 0$ and
$V \ne \emptyset$). The objective is bounded on this set
([bound](vector-objective-le-sum-abs.md)), and when the set is nonempty the supremum is attained,
by compactness. Goemans and Williamson take $m = n = |V|$; any $m \ge n$ gives the same value, since
$n$ vectors span at most $n$ dimensions, and for such $m$ the value is that of a semidefinite
program, which, for integral weights, Goemans and Williamson compute to any accuracy
$\varepsilon > 0$ in time polynomial in the input size and $\log(1/\varepsilon)$. A smaller $m$
can give a smaller value: for $m = 1$ the unit vectors are the numbers $\pm 1$, and $Z_P$ is the
weight of a maximum cut.

## Background

- [Ellipsoid method](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/README.md):
  Goemans and Williamson solve (P) approximately as a semidefinite program; for integral weights
  and accuracy $\varepsilon > 0$, the ellipsoid method of Grötschel, Lovász and Schrijver is one
  of the algorithms that do this in time polynomial in the input size and $\log(1/\varepsilon)$.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2 and §4.
