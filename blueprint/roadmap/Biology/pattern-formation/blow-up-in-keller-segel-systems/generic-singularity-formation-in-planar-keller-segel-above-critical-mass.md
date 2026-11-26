# Generic singularity formation in planar Keller–Segel above critical mass

**Model.** On a surface or bounded planar domain $\Sigma$ of area $A$, the Neumann–Poisson (Jäger–Luckhaus) Keller–Segel system with mass normalized to one and chemotactic strength $\beta>0$ is
$$\partial_t\rho=\Delta\rho-\beta\,\nabla\cdot(\rho\nabla c),\qquad -\Delta c=\rho-A^{-1},\qquad \int_\Sigma\rho=1,\quad\int_\Sigma c=0,$$
with $\partial_\nu c=0$ and no-flux for $\rho$ on $\partial\Sigma$. The constant $A^{-1}$ is an equilibrium for every $\beta$, and smooth equilibria exist at every mass. The state space $X$ is the set of strictly positive densities in $H^s(\Sigma)$, $1<s<3/2$, of unit mass.

**Theorem (disk).** Let $\Sigma$ be a Euclidean disk and $\beta\ge4\pi$. There is an open dense set $\mathcal O_\beta\subset X$ such that every solution starting in $\mathcal O_\beta$ either blows up in finite time ($\|\rho(t)\|_{L^\infty}\to\infty$ as $t\uparrow T_{\max}<\infty$) or grows up in infinite time ($\|\rho(t)\|_{L^\infty}\to\infty$ as $t\to\infty$). The threshold is sharp: for $0<\beta<4\pi$ every solution is global and uniformly bounded.

**Key identity.** For every smooth equilibrium $p$ on the unit disk $\mathbb D$, two explicit conformal variations $\eta_1,\eta_2$ satisfy
$$Q_p(\eta_1)+Q_p(\eta_2)=8-\frac{\beta}{\pi}\Bigl(2+\int_{\mathbb D}(1-|x|^2)^2p\,dx\Bigr),$$
where $Q_p$ is the second variation of the Keller–Segel free energy at $p$; hence every smooth equilibrium is linearly unstable for $\beta\ge4\pi$, without symmetry assumptions.

**Other geometries.** All smooth equilibria are linearly unstable on every smooth bounded planar domain for $\beta\ge8\pi$, and on a closed surface for $\beta$ above the conformal first-eigenvalue bound $\Lambda_1([g_0])$. On the round sphere the threshold is $8\pi$: above it every equilibrium is unstable, below it the uniform density is locally exponentially stable.

## Expansion

The system is the gradient flow of the free energy $\int\rho\log\rho-\frac\beta2\int\rho c$. A semiflow on $X$ whose equilibria are all linearly unstable cannot converge to an equilibrium from an open dense set of data, so solutions there must become unbounded. The disk identity follows from testing the second variation with the infinitesimal Möbius dilations, whose second variation can be computed exactly. The value $4\pi$ is half of the whole-plane critical value $8\pi$, matching the mass needed for a concentration point on the boundary.

## Sources

- Beomjun Choi and Geuntaek Seo, "Generic singularity formation in two-dimensional Keller-Segel systems", arXiv:2611.14237 (2026), Theorem 1.1, Theorem 1.2, Theorem 3.1, Theorem 4.1, Proposition 4.3 and Theorem 4.7, <https://doi.org/10.48550/arXiv.2611.14237>.
