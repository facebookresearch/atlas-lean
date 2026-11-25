# Forward invariance and global existence for the chemostat

Let $D, y, \mu_m, K_s > 0$ and $S_f \ge 0$, put $\mu(S) = \mu_m S/(K_s + S)$, and consider the chemostat

$$X' = \bigl(\mu(S) - D\bigr)X, \qquad S' = D(S_f - S) - \frac{1}{y}\,\mu(S)\,X,$$

with no death or maintenance terms. For every initial value with $X(0) \ge 0$ and $S(0) \ge 0$ the solution exists for
all $t \ge 0$ and stays in the closed quadrant $X \ge 0$, $S \ge 0$, and the substrate equivalent $Z = S + X/y$
satisfies $Z(t) \le \max(Z(0), S_f)$ for all $t \ge 0$.

The right-hand side is locally Lipschitz on the open set $S > -K_s$. On a maximal solution, $X(t) = X(0)\exp\int_0^t
(\mu(S) - D)$ keeps the sign of $X(0)$, and at $S = 0$ with $X \ge 0$ one has $S' = D S_f \ge 0$, so the quadrant is
forward invariant. By the substrate-equivalent identity $Z(t) = S_f + (Z(0) - S_f)e^{-Dt}$, the solution stays in the
compact set $\{X, S \ge 0,\ S + X/y \le \max(Z(0), S_f)\}$, so it cannot leave every compact set and therefore exists
for all $t \ge 0$.

## Depends on

## Proof depends on

- [Chemostat: the total substrate equivalent relaxes to the feed](chemostat-total-substrate-reduction.md), for $Z$
- [Solutions of locally Lipschitz ODEs that leave every compact set](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-maximal-solution-exit-compact.md), for global existence

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 10.5, Equation 10.18 (the chemostat model with Monod growth, p. 596).
- H. L. Smith and P. Waltman, *The Theory of the Chemostat: Dynamics of Microbial Competition*, Cambridge University Press, 1995, Chapter 1.
