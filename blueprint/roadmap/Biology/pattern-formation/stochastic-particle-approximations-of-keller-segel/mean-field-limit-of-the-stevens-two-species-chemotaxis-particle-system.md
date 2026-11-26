# Mean-field limit of the Stevens two-species chemotaxis particle system

**Target equation.** The doubly parabolic Keller–Segel system on $\mathbb R^2$,
$$\partial_t\rho=\Delta\rho-\chi\nabla\cdot(\rho\nabla c),\qquad \theta\partial_tc=\Delta c-\lambda c+\rho,$$
with $\rho_0$ a probability measure, $c_0\in L^1\cap L^\infty$ nonnegative, sensitivity $\chi>0$, time-scale ratio $\theta>0$ and decay rate $\lambda\ge0$.

**Particle system (2SKS).** $N$ cells start i.i.d. with law $\rho_0$ and about $NM\|c_0\|_{L^1}$ chemoattractant particles start i.i.d. with law $c_0/\|c_0\|_{L^1}$. Each cell emits chemoattractant particles at its own position according to a Poisson process of rate $M/\theta$; each chemoattractant particle moves as a Brownian motion with diffusion coefficient $\sqrt{2/\theta}$ and dies at rate $\lambda/\theta$. Each cell moves as a Brownian motion with diffusion coefficient $\sqrt2$ plus the drift $\chi\,(\nu_t*\nabla\phi_\varepsilon)(X^i_t)$, where $\nu_t$ is the chemoattractant empirical measure normalized by $NM$ and $\phi_\varepsilon$ is a mollifier at scale $\sqrt\varepsilon$.

**Theorem.** Assume the mollifier family satisfies the paper's mild integrability assumption and that $\chi<\chi^*_\theta$, an explicit small-sensitivity threshold. Fix $\sigma\in(0,\frac12]$.
1. *(Keller–Segel limit)* If $N\to\infty$ with $\varepsilon_N\to0$, $NM_N\varepsilon_N^{3+\sigma}\to\infty$ and $NM_N^{1+\sigma}\varepsilon_N^{2+\sigma}\to\infty$, then the empirical laws of cell trajectories are tight in $\mathcal P(C(\mathbb R_+,\mathbb R^2))$, and every limit point is almost surely a solution of the nonlinear martingale problem associated with the Keller–Segel system above (with initial data $\rho_0,c_0$).
2. *(Non-Markovian one-species limit)* For fixed $N$, if $M\to\infty$, $\varepsilon\to0$ and $M\varepsilon^{3+\sigma}\to\infty$, the cell trajectories are tight and every limit point is the one-species Talay–Tomašević system, in which each cell is attracted by the whole past paths of the other cells through the heat-kernel-weighted interaction $\int_0^t\nabla K_{t-s}(X^i_t-X^j_s)\,ds$.

## Expansion

The chemoattractant field felt by a cell is a Poisson-type average over emitted particles; as $M\to\infty$ it concentrates on its mean, which is a time integral of the heat kernel along the cells' past paths, giving the path-guided attraction of the one-species model. The singular kernel requires uniform-in-parameters bounds on expected negative moments of inter-particle distances, $\mathbb E\int_0^T|X^1_s-X^2_s|^{-2(\gamma-1)}ds$ with $\gamma\in(3/2,2)$, which close only for small $\chi$. Tightness plus identification of the drift then gives both limits.

## Sources

- Nicolas Fournier and Milica Tomašević, "Asymptotics of a two-species particle system associated to the doubly parabolic Keller-Segel equation in the plane", arXiv:2607.25986 (2026), Section 1, Section 2 main theorem (Theorem 5) and Propositions 9–10, <https://doi.org/10.48550/arXiv.2607.25986>.
