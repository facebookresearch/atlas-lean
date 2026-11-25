# Validity and attainment of Benders cuts

For the recourse value $Q(x) = \inf\{q^{\mathsf T}y : Wy = h - Tx,\ y \ge 0\}$ in the extended reals ($+\infty$ when the recourse problem is infeasible, $-\infty$ when it is unbounded below), every $\pi$ with $W^{\mathsf T}\pi \le q$ gives $Q(x) \ge \pi^{\mathsf T}(h - Tx)$ for every $x$, a valid affine lower cut; the existence of such a $\pi$ excludes $Q(x) = -\infty$, and when $Q(x)$ is finite some dual feasible $\pi$ attains it. Finite termination of a cutting-plane method is a separate statement that needs a finite enumeration of the dual extreme points.

## Proof depends on

- [Weak duality](../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-le-primal-value.md): weak duality for the cut.
- [Strong linear programming duality](strong-linear-programming-duality.md): strong duality for the attained cut, after writing the equality constraints as paired inequalities.

## Expansion

- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
