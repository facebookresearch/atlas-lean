# Geodesic representation of eikonal activation and identification of activation sites

**Model.** On a domain $\Omega \subset \mathbb R^d$ ($d \ge 2$, the myocardium) with conduction tensor $D \in C^1(\bar\Omega,\mathrm{Sym}^{d\times d})$, $\lambda_*I \preceq D(x) \preceq \lambda^*I$, and a set $E = \{(x_i,t_i)\}_{i=1}^N$ of earliest activation sites with times in $[T_{\min},T_{\max}]$, the activation map $\phi_E$ is the viscosity solution of

$$\sqrt{D(x)\nabla\phi_E(x)\cdot\nabla\phi_E(x)} = 1 \quad (x \in \Omega\setminus\{x_1,\dots,x_N\}), \qquad \phi_E(x_i) = t_i.$$

**Representation.** With the geodesic distance $\delta(x,y) = \inf\{L(\gamma) : \gamma(0) = x, \gamma(1) = y\}$, $L(\gamma) = \int_0^1\|\dot\gamma(t)\|_{D^{-1}(\gamma(t))}dt$ (Riemannian metric $\langle v,w\rangle_x = D^{-1}(x)v\cdot w$),

$$\phi_E(x) = \min_{i}\big(t_i + \delta(x,x_i)\big),$$

which requires the compatibility $t_i - t_j \le \delta(x_i,x_j)$ for all pairs. The map $(x,x_1,\dots,x_N,t_1,\dots,t_N) \mapsto \phi_E(x)$ is bounded and Lipschitz on the compact parameter set.

**Theorem.**
1. *(Existence.)* For any uniformly continuous objective $J$ on activation maps (e.g. least-squares mismatch with mapped activation times, or with a simulated ECG), $m_N = \min_E J(\phi_E)$ over $N$ sites is attained.
2. *(Monotonicity in $N$.)* $m_N$ is non-increasing in $N$; for $N \le N_{\max}$ the overall minimum is attained.
3. *(Gradient.)* Where geodesics are unique and smooth, with $w = \mathrm{Log}_x(y)$ the initial velocity of the geodesic from $x$ to $y$,

    $$\nabla_x\delta(x,y) = -\frac{D^{-1}(x)\,w}{\|w\|_{D^{-1}(x)}},$$

    so in the interior of the region of influence $R_i = \{x : \phi_E(x) = t_i + \delta(x,x_i)\}$ one has $\nabla_{x_i}\phi_E(x) = \nabla_{x_i}\delta(x_i,x)$ and $\partial_{t_i}\phi_E(x) = 1$.

## Depends on

- [Viscosity solution of a first-order equation](../../../Analysis/partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/is-viscosity-solution.md)

## Proof depends on

- [The Hopf–Lax formula](../../../Analysis/partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/hopf-lax-is-viscosity-solution.md)

## Expansion

The min-plus formula is the Hopf–Lax representation of the eikonal (Hamilton–Jacobi) equation: each site emits a front travelling at unit speed in the metric $D^{-1}$, and the first arrival wins; incompatible data would require a site to fire after the front from another site had already passed it. Continuity of $\phi_E$ in the sites plus compactness gives existence; duplicating a site shows that adding sites never hurts. The gradient follows from the first variation of arc length, the boundary term at the moved endpoint being the unit tangent; geodesics are traced back from $x$ along $-D\nabla\phi$ to evaluate the logarithm map, which makes gradient descent on site positions and times practical.

## Sources

- T. Grandits, A. Effland, T. Pock, R. Krause, G. Plank, S. Pezzuto, "GEASI: Geodesic-based earliest activation sites identification in cardiac models", International Journal for Numerical Methods in Biomedical Engineering 37(8) (2021) e3505, Section 2, Eqs (1)–(13), Lemma 1, Theorem 1, Proposition 1, Corollary 1 and Proposition 2, <https://doi.org/10.1002/cnm.3505>, PMCID PMC8459297.
