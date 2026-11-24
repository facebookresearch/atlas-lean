# Consistency of sample average approximation over finitely many decisions; validity of Benders cuts

(Sample average approximation.) Let $X$ be finite and nonempty, and let $\xi_1, \xi_2, \dots$ be i.i.d. with $C(x, \xi_1)$ integrable for each $x$, $f(x) = E[C(x, \xi_1)]$ and $\hat f_N(x) = N^{-1}\sum_{i \le N}C(x, \xi_i)$. Almost surely $\max_x|\hat f_N(x) - f(x)| \to 0$, and for all large $N$ every minimizer of $\hat f_N$ minimizes $f$. (Benders cuts.) For the recourse value $Q(x) = \inf\{q^{\mathsf T}y : Wy = h - Tx,\ y \ge 0\}$ in the extended reals ($+\infty$ when the recourse problem is infeasible, $-\infty$ when it is unbounded below), every $\pi$ with $W^{\mathsf T}\pi \le q$ gives $Q(x) \ge \pi^{\mathsf T}(h - Tx)$ for every $x$, a valid affine lower cut; the existence of such a $\pi$ excludes $Q(x) = -\infty$, and when $Q(x)$ is finite some dual feasible $\pi$ attains it. Finite termination of a cutting-plane method is a separate statement that needs a finite enumeration of the dual extreme points.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md): almost-sure convergence for each of the finitely many $x$, after transporting the i.i.d. sequence to the coordinate process of the product law.
- [Weak duality](../lagrange-duality/dual-value-le-primal-value.md): weak duality for the cut.
- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md): strong duality for the attained cut, after writing the equality constraints as paired inequalities.
