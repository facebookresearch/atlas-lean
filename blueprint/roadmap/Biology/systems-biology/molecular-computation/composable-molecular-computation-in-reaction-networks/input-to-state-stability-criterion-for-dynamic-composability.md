# Input-to-state stability criterion for dynamic composability

**Setting.** A steady-state chemical reaction computation (msCRC) $\mathscr{C}^1$ computes a value $\bar y^1$ as the limit of its output species $y^1$ under $\dot x^1 = f^1(x^1,y^1)$, $\dot y^1 = g^1(x^1,y^1)$. A second msCRC $\mathscr{C}^2$ reads $y^1$ as its input, $\dot y^2 = g^2(y^1, y^2)$, and computes $\bar y^2$ from the input value $\bar y^1$. The pair is *composable* if $\bar y^2$ is the value of the composite function, and *dynamically composable* if, running all reactions in parallel,

$$\lim_{t\to\infty}\bigl(y^1(t), y^2(t)\bigr) = (\bar y^1, \bar y^2),$$

i.e. the downstream layer need not wait for the upstream layer to finish. Throughout, the layers are composable (the output species of $\mathscr{C}^1$ are the input species of $\mathscr{C}^2$, and no output species of $\mathscr{C}^2$ is an input species of $\mathscr{C}^1$) and satisfy two standing assumptions: (A.1) run separately, $\mathscr{C}^1$ follows $\dot x^1=f^1(x^1,y^1)$, $\dot y^1=g^1(x^1,y^1)$ from $(x^1_0,y^1_0)$, and $\mathscr{C}^2$ follows $\dot x^2=0$, $\dot y^2=g^2(x^2,y^2)$ from $x^2(0)=\bar y^1$, $y^2(0)=y^2_0$, so its input species act as catalysts; (A.2) along these separate runs $y^1(t)\to\bar y^1$ and $y^2(t)\to\bar y^2$. The coupled system is $\dot x^1=f^1(x^1,y^1)$, $\dot y^1=g^1(x^1,y^1)$, $\dot y^2=g^2(y^1,y^2)$ from $(x^1_0,y^1_0,y^2_0)$.

**Theorem (ISS Lyapunov criterion).** For a mass-action system $\dot s = f(u(t), s)$ driven by an input with $u(t) \to \bar u$, let $s(t)$ be bounded and $\bar s > 0$ the unique equilibrium of $\dot s = f(\bar u, s)$ in its stoichiometric class $(s_0 + \mathscr{S}) \cap \mathbb{R}^n_{>0}$. If $V$ is an ISS-Lyapunov function with respect to $(\bar u, \bar s)$, then either $s(t) \to \bar s$ or $s(t) \to \partial\mathbb{R}^n_{\ge 0}$; if $s$ is persistent, $s(t) \to \bar s$. Consequently, if the $y^2$-part of the coupled system is ISS with respect to $(\bar y^1,\bar y^2)$, the two layers are dynamically composable.

**Theorem (deficiency zero).** If the reduced system $\tilde{\mathscr{C}}^2$ of the downstream layer is weakly reversible with deficiency zero and its trajectory is persistent, the layers are dynamically composable. Persistence, and hence dynamic composability, holds in particular if $\tilde{\mathscr{C}}^2$ has a single linkage class, has only two species, has a two-dimensional stoichiometric subspace, or is strongly endotactic.

**Nonzero deficiency.** For a one-species downstream layer that is a birth-death network with $\kappa_0 > 0$ and dominating degradation (more degradation than production orders, or equal orders with larger constant degradation coefficient), whose steady-state equation $g^2(\bar y^1, s) = 0$ has a unique positive, non-degenerate root, the layers are dynamically composable.

## Depends on

- [Unique complex-balanced equilibrium of a deficiency-zero network](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium-of-deficiency.md)

## Expansion

Composability is an asymptotically autonomous problem: the downstream layer sees an input converging to $\bar y^1$, and ISS converts input convergence into state convergence. For weakly reversible deficiency-zero networks the pseudo-Helmholtz free energy relative to the complex-balanced equilibrium is a natural Lyapunov function, and the perturbation from a time-varying input enters as a vanishing term, which gives an ISS-type estimate. The only remaining failure mode is drift to the boundary, which persistence results (single linkage class, low dimension, strong endotacticity) exclude.

## Sources

- R. Jiang, C. Gao, D. Dochain, "Structure-conditioned input-to-state stability for layer-by-layer molecular computations in parallel chemical reaction networks", *Automatica* 193 (2026), 113224, definition of dynamic composability, Theorem 3.1 (cited), Theorem 3.2, Corollary 3.1, Theorem 4.1, Corollary 4.1 and Theorem 5.1, <https://doi.org/10.1016/j.automatica.2026.113224> (preprint arXiv:2512.07116).
