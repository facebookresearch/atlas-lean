# Multiphase Hele–Shaw limit of the multispecies Keller–Segel system

**Model.** Let $\Omega \subset \mathbb{R}^d$ be a bounded domain, $N \ge 1$ species with densities $\rho_i^\varepsilon \ge 0$, $m > 2$, $\sigma > 0$, $f_m(s) = s^m/(m-1)$, and a symmetric interaction matrix $A = (\alpha_{ij})$. With Neumann (no-flux) conditions,
$$\varepsilon\,\partial_t \rho_i^\varepsilon - \nabla\cdot\big(\rho_i^\varepsilon \nabla f_m'(\rho_1^\varepsilon + \dots + \rho_N^\varepsilon)\big) + \nabla\cdot\Big(\rho_i^\varepsilon \sum_{j=1}^N \alpha_{ij}\nabla\phi_j^\varepsilon\Big) = 0, \qquad \sigma\phi_j^\varepsilon - \varepsilon^2\Delta\phi_j^\varepsilon = \rho_j^\varepsilon,$$
which preserves the masses $m_i = \int_\Omega \rho_i^\varepsilon$. Assume (A1) $A$ is symmetric positive semidefinite; (A2) no two columns of $A$ coincide and no column vanishes (so $\alpha_{ii} > 0$); and the vacuum condition $\sum_i m_i/\theta_i < |\Omega|$ with $\theta_i = (\alpha_{ii}/(2\sigma))^{1/(m-2)}$.

**Energies.** With $\vec a = (a_i)$, $a_i = \frac{m-2}{m-1}(\alpha_{ii}/(2\sigma))^{(m-1)/(m-2)}$, and $f(\vec\rho) = f_m(\sum_i \rho_i)$ on $\mathbb{R}^N_{\ge0}$ ($+\infty$ elsewhere), the system is the Wasserstein gradient flow of
$$\mathcal{E}^\varepsilon(\vec\rho) = \frac1\varepsilon\int_\Omega f(\vec\rho) + \vec a\cdot\vec\rho - \tfrac12\,\vec\rho^{\,T} A\,\vec\phi^\varepsilon\,dx$$
(set to $+\infty$ unless $\int_\Omega \vec\rho = \vec m$). The limit energy, on configurations $\vec\rho = (\theta_1\chi_{E_1},\dots,\theta_N\chi_{E_N})$ with disjoint finite-perimeter sets $E_i$ of the prescribed masses and vacuum $E_0 = \Omega \setminus \bigcup_i E_i$, is
$$\mathcal{E}^0(\vec\rho) = \sum_{i,j=0}^N \sigma_{ij}\,\mathcal{H}^{d-1}(\partial^*E_i \cap \partial^*E_j \cap \Omega),$$
and $+\infty$ otherwise. The surface tensions are geodesic distances $\sigma_{ij} = d_A(\theta_i e_i, \theta_j e_j)$ (with $\theta_0 e_0 = 0$), where
$$d_A(\zeta_0,\zeta_1) = \inf_\gamma \frac{1}{\sqrt2}\int_0^1 \sqrt{H(\gamma(t))}\,|\gamma'(t)|_A\,dt, \qquad H(\phi) = \frac\sigma2|\phi|_A^2 - f^*(A\phi - \vec a),$$
over piecewise $C^1$ paths from $\zeta_0$ to $\zeta_1$, with $|\phi|_A^2 = \phi^T A\phi$ and $f^*(v) = \big(\tfrac{m-1}{m}\max\{v_1,\dots,v_N,0\}\big)^{m/(m-1)}$.

**Theorem.** Assume (A1), (A2), the vacuum condition, $m > 2$, and well-prepared data: $\sup_{\varepsilon}\mathcal{E}^\varepsilon(\vec\rho^{\,\varepsilon}_{in}) \le M$ and $\vec\rho^{\,\varepsilon}_{in} \to \sum_i \theta_i\chi_{E_{i,in}} e_i$. Let $\vec\rho^{\,\varepsilon}$ be solutions (more generally, any family satisfying the energy inequality, the individual continuity equations and the total-flux identity). Then, along a subsequence:
1. $\vec\rho^{\,\varepsilon} \to \vec\rho$ strongly in $L^\infty_{loc}(0,\infty; L^1(\Omega)^N)$, with $\vec\rho(t) = \sum_i \theta_i\chi_{E_i(t)}e_i$ for a finite-perimeter partition $\{E_i(t)\}_{i=0}^N$ and $\mathcal{E}^0(\vec\rho(t)) \le M$;
2. there are velocity fields $v_i \in L^2(\chi_{E_i}\,dx\,dt)$ with $\partial_t\chi_{E_i} + \nabla\cdot(\chi_{E_i}v_i) = 0$, no flux through $\partial\Omega$, and the dissipation inequality $\mathcal{E}^0(\vec\rho(t)) + \sum_i \frac12\int_0^t\!\int_\Omega \rho_i|v_i|^2 \le \mathcal{E}^0(\vec\rho_{in})$;
3. the rescaled pressure $p^\varepsilon = \varepsilon^{-1}\big(\rho^\varepsilon f_m'(\rho^\varepsilon) + \vec a\cdot\vec\rho^{\,\varepsilon} - (\vec\rho^{\,\varepsilon})^T A\vec\phi^\varepsilon\big)$ converges weakly-* to some $p$ in $L^2_{loc}(0,\infty;(C^s)^*)$ for every $s \in (0,1)$;
4. if moreover $\int_0^T\mathcal{E}^\varepsilon(\vec\rho^{\,\varepsilon}(t))\,dt \to \int_0^T\mathcal{E}^0(\vec\rho(t))\,dt$, the total flux $j = \sum_i \rho_i v_i$ and $p$ satisfy, for all test fields $\xi$ tangent to $\partial\Omega$,
$$\int_0^T\!\!\int_\Omega j\cdot\xi - p\,\nabla\cdot\xi\,dx\,dt = -\int_0^T\sum_{i,j=0}^N \sigma_{ij}\int_\Omega\big(\nabla\cdot\xi - \nu_{ij}\otimes\nu_{ij} : D\xi\big)\,d\mu_{ij}\,dt,$$
with $\mu_{ij} = \mathcal{H}^{d-1}$ restricted to $\partial^*E_i \cap \partial^*E_j \cap \Omega$ and $\nu_{ij}$ its normal. This is the weak form of the multiphase Hele–Shaw problem with surface tension: Darcy flow inside each phase, pressure jumps $\sigma_{ij}$ times mean curvature across interfaces, and Young's contact-angle balance at triple junctions.

## Depends on

- [Γ-convergence of the multispecies Keller–Segel energy to an interfacial energy](gamma-convergence-of-the-multispecies-keller-segel-energy-to-an-interfacial-energy.md)

## Expansion

The time rescaling $(x,t) \mapsto (\varepsilon x, \varepsilon^3 t)$ makes this a long-time, large-scale limit. Compactness follows from the uniform energy bound and the dissipation. The individual fluxes $\rho_i\nabla f_m'(\rho)$ cannot be identified, but only their sum $\rho\nabla f_m'(\rho)$ enters the limit equation, and it is controlled because the total density is compact; phase separation in the limit removes the ambiguity. Under the energy convergence assumption, a classical device for lack of control on free boundaries, the first variation of $\mathcal{E}^\varepsilon$ passes to the first variation of $\mathcal{E}^0$, giving the curvature and contact-angle conditions.

## Sources

- J. Jang and A. Mellet, "Cell-cell adhesion and multiphase Hele–Shaw problem as the singular limit of a Keller–Segel system", arXiv:2606.10205 (2026), Theorem 1.3 (proved in Section 6; the solution concept is checked for limits of the JKO scheme in Appendix A), <https://doi.org/10.48550/arXiv.2606.10205>.
