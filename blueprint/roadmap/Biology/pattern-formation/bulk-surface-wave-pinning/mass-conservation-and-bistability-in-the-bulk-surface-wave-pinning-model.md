# Mass conservation and bistability in the bulk-surface wave-pinning model

**Model.** Let $\Omega \subset \mathbb{R}^d$ ($d = 2,3$) be a cell with smooth membrane $\Gamma = \partial\Omega$ and outward normal $\mathbf{n}$. A small GTPase switches between an inactive cytosolic form $b(\mathbf{x},t)$, diffusing in the bulk, and an active membrane-bound form $a(\mathbf{x},t)$, diffusing on the membrane. All reactions occur on $\Gamma$:

$$\partial_t b = D_b \Delta b \ \text{ in } \Omega, \qquad -D_b\, \mathbf{n}\cdot\nabla b = f(a,b) \ \text{ on } \Gamma, \qquad \partial_t a = D_a \Delta_\Gamma a + f(a,b) \ \text{ on } \Gamma,$$

where $\Delta_\Gamma$ is the Laplace–Beltrami operator, $D_b \gg D_a > 0$, and

$$f(a,b) = \omega\Big(k_0 + \frac{\gamma a^n}{K^n + a^n}\Big) b - \beta a, \qquad \omega = \frac{|\Omega|}{|\Gamma|},$$

with basal and cooperative activation rates $k_0, \gamma > 0$, Hill coefficient $n$ (typically $n = 2$), half-saturation $K > 0$ and inactivation rate $\beta > 0$.

**Proposition.**

1. *Conservation of mass.* For every solution,

$$M(t) = \int_\Omega b(\mathbf{x},t)\, d\mathbf{x} + \int_\Gamma a(\mathbf{x},t)\, ds = M_0 \quad \text{for all } t \ge 0.$$

2. *Well-mixed reduction.* Spatially homogeneous solutions $a_g(t), b_g(t)$ satisfy $\dot a_g = f(a_g, b_g)$, $\omega \dot b_g = -f(a_g, b_g)$, with conserved scaled total $a_g/\omega + b_g = M_0/|\Omega|$.
3. *Bistability.* For $n = 2$ there are $0 < b_1 < b_2$ such that for each fixed $\bar b \in (b_1, b_2)$ the map $a \mapsto f(a, \bar b)$ can have three zeros $a_1(\bar b) < a_2(\bar b) < a_3(\bar b)$, with

$$\partial_a f(a_1, \bar b) < 0, \qquad \partial_a f(a_2, \bar b) > 0, \qquad \partial_a f(a_3, \bar b) < 0,$$

so the membrane kinetics at fixed cytosolic level are bistable, with stable low and high activity states.

## Expansion

Integrating the bulk equation over $\Omega$ and using the divergence theorem with the Robin condition gives $\frac{d}{dt}\int_\Omega b = -\int_\Gamma f$, while integrating the surface equation over the closed manifold $\Gamma$ gives $\frac{d}{dt}\int_\Gamma a = \int_\Gamma f$; they cancel. Mass conservation plus bistability plus the disparity $D_b \gg D_a$ is the wave-pinning mechanism: a front between the high and low states of $a$ travels on the membrane while consuming the fast-diffusing bulk pool, until $b$ drops to the level where the front stalls, leaving a polarized steady state. The bulk geometry enters through $\omega$, which is largest for round cells, so activation is favoured in resting cells.

## Sources

- D. Cusseddu, L. Edelstein-Keshet, J. A. Mackenzie and S. Portet, "A coupled bulk-surface model for cell polarisation", arXiv:1809.04535 (2018), Section 2 (model, Theorem 2.1, Propositions 2.1 and 2.2) and Section 4.1 (well-mixed model), <https://doi.org/10.48550/arXiv.1809.04535>.
