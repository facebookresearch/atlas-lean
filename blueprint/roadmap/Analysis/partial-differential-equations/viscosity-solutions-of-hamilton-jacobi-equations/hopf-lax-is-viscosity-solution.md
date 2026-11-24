# The Hopf–Lax formula

Let $H$ be a convex Hamiltonian on the dual of a finite-dimensional real inner
product space with $H(p)/|p| \to \infty$, let $L(v) = \sup_p (p(v) - H(p))$ be its Legendre transform,
and let $g$ be bounded and Lipschitz. Then

$$u(x, t) = \inf_y \Big( t\, L\Big(\frac{x - y}{t}\Big) + g(y) \Big)$$

is a viscosity solution of $u_t + H(D_x u) = 0$ on $E \times (0, \infty)$, and $u(x', t) \to g(x)$ as
$(x', t) \to (x, 0)$ with $t > 0$. Calder also states that it is the unique viscosity solution;
uniqueness is not part of the statement above.

The formula is the value function of the calculus-of-variations problem
$\inf\{g(y(0)) + \int_0^t L(\dot y)\, ds : y(t) = x\}$, and the viscosity inequalities follow from its
dynamic programming principle $u(x, t) = \min_y ((t - s) L(\frac{x - y}{t - s}) + u(y, s))$, as in
Calder's sketch.

## Background

- [Fenchel conjugate](../../convex-analysis-and-variations/fenchel-moreau-theorem/fenchel-conj.md):
  $L$ is the convex conjugate of $H$, and $H = L^*$ by the Fenchel–Moreau theorem; here both are
  real valued, so the statement writes the supremum directly.
- [Linear quadratic regulator](../../../ComputerScience/machine-learning/reinforcement-learning/linear-quadratic-regulator/README.md):
  dynamic programming in discrete time, where the Riccati recursion plays the role of the
  Hamilton–Jacobi–Bellman equation for quadratic value functions.
- [Kantorovich duality](../../../MeasureTheory/optimal-transport/kantorovich-duality/README.md):
  for $H(p) = |p|^2/2$ the formula is $u(x, t) = \inf_y (g(y) + |x - y|^2 / 2t)$, an
  inf-convolution of $g$ with the quadratic cost $|x - y|^2/2t$, the operation that defines
  $c$-transforms (up to sign conventions) in the dual problem of optimal transport.

## Sources

- J. Calder, *Lecture notes on viscosity solutions*, University of Minnesota, version of 30 July 2024, §6.2, which defers the complete proof to L. C. Evans, *Partial Differential Equations*, Chapter 10.
- E. Hopf, "Generalized solutions of non-linear equations of first order", J. Math. Mech. 14 (1965), 951–973.
- P. D. Lax, "Hyperbolic systems of conservation laws II", Comm. Pure Appl. Math. 10 (1957), 537–566.
