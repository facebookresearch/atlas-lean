# Static sharp-interface limit of volume-filling Keller–Segel

**Model.** The volume-filling Keller–Segel system

$$\partial_tu-\delta\Delta\frac{u^m}{m}+\nabla\cdot\bigl[\chi u(1-u)\nabla v\bigr]=0,\qquad -D\Delta v+v=u$$

in a bounded domain $\Omega$ with no-flux conditions, under the scaling $\delta=1$, $D=\varepsilon^2$, $\chi=\varepsilon^{-1}$ (strong aggregation and short-range signal), $m\ge1$.

**Theorem.** Let $\widetilde\Omega\subset\Omega$ be a nontrivial set of finite perimeter, take $u_\varepsilon^0=\mathbf 1_{\widetilde\Omega}$, and assume the rescaled free energies $\mathscr J_\varepsilon(u^0_\varepsilon)$ are bounded uniformly in $\varepsilon\in(0,1]$. Then, along a subsequence, energy solutions satisfy

$$u_\varepsilon,\ v_\varepsilon\to u\quad\text{strongly in }L^\infty\bigl((0,T);L^1(\Omega)\bigr),$$

and the limit is time independent: $u=\mathbf 1_{\widetilde\Omega}\in BV(\Omega;\{0,1\})$ almost everywhere. Characteristic patches are frozen on fixed time intervals.

**Hyperbolic regime.** With $D=1$ and vanishing cell diffusion $\delta=\varepsilon$, solutions converge strongly in every $L^p$ to an entropy-type solution of the hyperbolic–elliptic Keller–Segel system $\partial_tu+\nabla\cdot[\chi u(1-u)\nabla v]=0$, $-\Delta v+v=u$, identified through a kinetic formulation.

## Expansion

The rescaled free energy behaves like a Modica–Mortola functional: the double-well structure created by volume filling makes $\{0,1\}$-valued states the only finite-energy limits, and the interfacial cost is proportional to perimeter. The energy-dissipation bound shows that any motion costs dissipation of order $\varepsilon^{-1}$ per unit time, so on fixed time intervals the patch cannot move; interface motion would only appear on longer time scales.

## Depends on

- [Nonlinear diffusion limit of volume-filling Keller–Segel](nonlinear-diffusion-limit-of-volume-filling-keller-segel.md)

## Sources

- Mingyue Zhang, "Three asymptotic regimes for a Keller–Segel system with volume-filling effect", arXiv:2609.04599 (2026), Sections 4–5, Theorems 7 and 12, <https://doi.org/10.48550/arXiv.2609.04599>.
