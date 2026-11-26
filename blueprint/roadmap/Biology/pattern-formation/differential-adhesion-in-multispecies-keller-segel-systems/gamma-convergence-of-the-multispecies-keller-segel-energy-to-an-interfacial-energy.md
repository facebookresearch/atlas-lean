# Γ-convergence of the multispecies Keller–Segel energy to an interfacial energy

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

**Theorem.** Under (A1), (A2) and the vacuum condition, $\mathcal{E}^\varepsilon$ Γ-converges to $\mathcal{E}^0$ in the strong $L^1(\Omega)^N$ topology as $\varepsilon \to 0$: for every $\vec\rho^{\,\varepsilon} \to \vec\rho^{\,0}$ in $L^1$, $\liminf_{\varepsilon\to0}\mathcal{E}^\varepsilon(\vec\rho^{\,\varepsilon}) \ge \mathcal{E}^0(\vec\rho^{\,0})$; and for every $\vec\rho^{\,0}$ there is a recovery sequence with $\limsup_{\varepsilon\to0}\mathcal{E}^\varepsilon(\vec\rho^{\,\varepsilon}) \le \mathcal{E}^0(\vec\rho^{\,0})$. In particular finite-energy limits are phase-separated: each species occupies its own region $E_i$ at the constant density $\theta_i$. Since the $\sigma_{ij}$ are geodesic distances they satisfy the triangle inequality $\sigma_{ij} \le \sigma_{ik} + \sigma_{kj}$, which makes $\mathcal{E}^0$ lower semicontinuous.

## Expansion

Completing the square rewrites $\mathcal{E}^\varepsilon(\vec\rho) = \frac1\varepsilon\int W(\vec\rho) + \frac{1}{2\sigma\varepsilon}\int(\vec\rho - \sigma\vec\phi^\varepsilon)^T A(\vec\rho - \sigma\vec\phi^\varepsilon) + \frac\varepsilon2\int(\nabla\vec\phi^\varepsilon)^T A\nabla\vec\phi^\varepsilon$ with the multi-well potential $W(\vec\rho) = f(\vec\rho) + \vec a\cdot\vec\rho - \frac{1}{2\sigma}\vec\rho^{\,T}A\vec\rho$, which under (A1)–(A2) is nonnegative and vanishes exactly at $0, \theta_1 e_1,\dots,\theta_N e_N$. Minimizing out $\vec\rho$ for fixed $\vec\phi$ produces a vector Allen–Cahn (Modica–Mortola) functional in $\vec\phi$ with potential built from $H$, to which Baldo's multiphase Γ-convergence theorem applies; the surface tension between two wells is the degenerate-metric geodesic distance $d_A$.

## Sources

- J. Jang and A. Mellet, "Cell-cell adhesion and multiphase Hele–Shaw problem as the singular limit of a Keller–Segel system", arXiv:2606.10205 (2026), Theorem 1.1, with Lemma 3.1, Proposition 3.2, Proposition 3.3 and Theorem 3.4 (Baldo's theorem), proved in Section 4, <https://doi.org/10.48550/arXiv.2606.10205>.
