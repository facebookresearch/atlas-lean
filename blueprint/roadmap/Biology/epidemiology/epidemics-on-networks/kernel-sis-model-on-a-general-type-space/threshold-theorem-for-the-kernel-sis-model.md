# Threshold theorem for the kernel SIS model on a general type space

Let $(\Omega, \mathscr F)$ be a measurable space of individual types (features), let $\kappa(x, \mathrm dy)$ be a non-negative transmission kernel and $\gamma : \Omega \to (0,\infty)$ a recovery rate. The **kernel (infinite-dimensional) SIS model** for the probability $u(t,x) \in [0,1]$ that an individual of type $x$ is infected at time $t$ is

$$\partial_t u(t,x) = (1 - u(t,x)) \int_\Omega u(t,y)\,\kappa(x,\mathrm dy) - \gamma(x)\,u(t,x), \qquad u(0,\cdot) = u_0 .$$

It contains the multigroup Lajmanovich–Yorke model (finite $\Omega$), SIS dynamics on a graph with bounded degrees, and SIS dynamics on a graphon $\kappa(x,\mathrm dy) = \beta(x) W(x,y) \theta(y)\,\mu(\mathrm dy)$.

**Hypotheses.**

- (A0) $\gamma$ is positive and bounded, and $\sup_{x \in \Omega} \kappa(x, \Omega) < \infty$.
- (A1) $\kappa(x,\mathrm dy) = k(x,y)\,\mu(\mathrm dy)$ for a finite positive measure $\mu$ and a measurable $k \ge 0$, and for some $q > 1$, $\sup_{x} \int_\Omega \big(k(x,y)/\gamma(y)\big)^q \,\mu(\mathrm dy) < \infty$.
- (A2) (connectivity) $\int_{A \times A^c} k(x,y)\,\mu(\mathrm dx)\,\mu(\mathrm dy) > 0$ for every measurable $A$ with $\mu(A) > 0$ and $\mu(A^c) > 0$.

The **next-generation operator** is $T_{k/\gamma} g(x) = \int_\Omega \frac{k(x,y)}{\gamma(y)} g(y)\,\mu(\mathrm dy)$ on bounded measurable functions, and the **basic reproduction number** is its spectral radius $R_0 = r(T_{k/\gamma})$.

**Theorem.**

1. Under (A0) the equation has a unique global solution, and $u(t,x) \in [0,1]$ for all $t \ge 0$, $x \in \Omega$, whenever $u_0$ takes values in $[0,1]$.
2. Under (A0) and (A1), if $R_0 \le 1$ then $u(t,x) \to 0$ as $t \to \infty$ for every $x \in \Omega$ (the disease dies out, including at criticality).
3. Under (A0), (A1) and (A2), if $R_0 > 1$ there is a unique equilibrium $g^* : \Omega \to [0,1]$ with $\int g^*\,d\mu > 0$; every solution with $\int u_0\,d\mu > 0$ converges pointwise to $g^*$, while a solution with $u_0 = 0$ $\mu$-a.e. converges pointwise to $0$.

When $\inf \gamma > 0$ the convergence in items 2–3 is uniform on $\Omega$. In the subcritical case $s(T_\kappa - \gamma) < 0$ the extinction is uniformly exponential: for every $c \in (0, -s(T_\kappa - \gamma))$ there is $\theta(c) < \infty$ with $\|u(t,\cdot)\|_\infty \le \theta\,\|u_0\|_\infty\,e^{-ct}$.

## Depends on

- [Spectral bound and reproduction number for infinite-dimensional population structure](../../next-generation-matrix-and-the-basic-reproductio/spectral-bound-and-reproduction-number-for-infinite-dimensional-structure.md)

## Expansion

The vector field $F(g) = (1-g)\,T_\kappa g - \gamma g$ is cooperative on $\Delta = \{0 \le g \le 1\}$, so the semiflow is order preserving and $\Delta$ is forward invariant. The solution from $u_0 \equiv 1$ decreases to the maximal equilibrium $g^*$, which dominates every equilibrium. Under (A1) the integral operator is weakly compact, so $r(T_{k/\gamma}) - 1$ and the spectral bound $s(T_k - \gamma)$ have the same sign and $R_0 > 1$ yields a positive eigenfunction $w$; small multiples $\varepsilon w$ are sub-solutions, giving $\int g^* d\mu > 0$. Connectivity makes every nonzero trajectory instantly $\mu$-a.e. positive, and a sublinearity argument then shows $g^*$ is the only nonzero equilibrium. At criticality ($R_0 = 1$) the maximal equilibrium is shown to vanish. Without (A2) the conclusion can fail: the paper exhibits a kernel with $R_0 = 1$ (spectral bound $0$) whose equilibria form a continuum.

## Sources

- Jean-François Delmas, Dylan Dronnier, Pierre-André Zitt, "An Infinite-Dimensional SIS Model", arXiv (2020). Assumptions 0–2, Section 1.3 (definition of $R_0$), Theorem 1.5, Proposition 4.1, Theorems 4.6, 4.7, 4.14 and 4.18, Propositions 4.15–4.16 (critical counterexample). <https://doi.org/10.48550/arXiv.2006.08241>. Published version: Journal of Differential Equations 313 (2022), 1–53, <https://doi.org/10.1016/j.jde.2021.12.024>; locators above refer to the arXiv version.
