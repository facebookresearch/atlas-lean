# Kinetic and Keller–Segel posteriors for the tumbling kernel agree in the diffusive limit

**Setting.** Reconstruct the tumbling-kernel pair $u = (K_0, K_1) \in \mathcal A$ of the kinetic chemotaxis model from noisy counts of the macroscopic bacterial density. Experiments $k = 1, \dots, K$ use initial data $f_0^{(k)} \in C^1_c(\mathbb R^3 \times V)$, nonnegative, and measurements $j$ are taken at times $t_j$ with compactly supported test functions $\chi_j \in C_c(\mathbb R^3)$:

$$\mathcal G^{\varepsilon,\mathrm{ch}}_{jk}(u) = \int_{\mathbb R^3}\int_V f^{(k)}_\varepsilon(x,t_j,v)\, dv\, \chi_j(x)\, dx, \qquad \mathcal G^{\mathrm{KS}}_{jk}(u) = \int_{\mathbb R^3}\rho^{(k)}(x,t_j)\, \chi_j(x)\, dx,$$

for the kinetic model and for its Keller–Segel limit (whose coefficients $D, \Gamma$ are computed from $u$). Assume $\|f_0^{(k)}\|_{L^1}, \|f_0^{(k)}\|_{L^\infty} < C_\rho$ and $\max\{\|\chi_j\|_{L^1}, \|\chi_j\|_{L^2}, \|\chi_j\|_{L^\infty}, |\operatorname{supp}\chi_j|\} < C_x$. Data are $y_{jk} = \mathcal G_{jk}(u) + \eta_{jk}$ with independent noise $\eta_{jk} \sim N(0, \gamma^2)$, and a prior $\mu_0$ on $\mathcal A$ is given. Let $\mu^y_{\varepsilon,\mathrm{ch}}$ and $\mu^y_{\mathrm{KS}}$ be the Bayesian posteriors with the kinetic and the Keller–Segel forward maps.

**Lemma.** Both measurement maps are bounded on $\mathcal A$ uniformly in $\varepsilon$ and, for small $\varepsilon$, Lipschitz in $u$ for $\|u\|_* = \max(\|K_0\|_\infty, \|K_1\|_\infty)$; both posteriors are well defined and mutually absolutely continuous. Moreover $\mathcal G^{\varepsilon,\mathrm{ch}} \to \mathcal G^{\mathrm{KS}}$ uniformly on $\mathcal A$ as $\varepsilon \to 0$.

**Theorem.** Under these hypotheses,

$$d_{\mathrm{KL}}\big(\mu^y_{\varepsilon,\mathrm{ch}},\ \mu^y_{\mathrm{KS}}\big) \longrightarrow 0 \qquad (\varepsilon \to 0),$$

and consequently the Hellinger distance $d_{\mathrm{Hell}}(\mu^y_{\varepsilon,\mathrm{ch}}, \mu^y_{\mathrm{KS}}) \to 0$ as well.

So in the diffusive regime the cheaper macroscopic model yields asymptotically the same posterior for the microscopic tumbling kernel; equally, the macroscopic data cannot resolve kernel features beyond those that determine $(D, \Gamma)$.

## Depends on

- [Parabolic limit of kinetic chemotaxis to the Keller–Segel equation](parabolic-limit-of-kinetic-chemotaxis-to-keller-segel.md)

## Proof sketch

With Gaussian noise the posterior density with respect to $\mu_0$ is $\exp(-\tfrac{1}{2\gamma^2}|y - \mathcal G(u)|^2)/Z$. The forward limit, uniform over $\mathcal A$, makes $\mathcal G^{\varepsilon,\mathrm{ch}} \to \mathcal G^{\mathrm{KS}}$ uniformly, since each measurement is a test-function integral of $\int_V f_\varepsilon\,dv \to \rho$. Uniform boundedness of the misfits makes the normalising constants $Z^{\varepsilon,\mathrm{ch}}$ and $Z^{\mathrm{KS}}$ bounded away from zero, and $Z^{\varepsilon,\mathrm{ch}} \to Z^{\mathrm{KS}}$. The log-density ratio $\log(d\mu^y_{\varepsilon,\mathrm{ch}}/d\mu^y_{\mathrm{KS}})$ then tends to zero uniformly on $\mathcal A$, so its integral, the KL divergence, vanishes. Hellinger convergence follows from $d_{\mathrm{Hell}}^2 \le \tfrac12 d_{\mathrm{KL}}$.

## Sources

- Kathrin Hellmuth, Christian Klingenberg, Qin Li and Min Tang, "Multiscale Convergence of the Inverse Problem for Chemotaxis in the Bayesian Setting", *Computation* 9 (2021), 119, <https://doi.org/10.3390/computation9110119>. Preprint version: arXiv:2110.13787 (2021), Section 3, Lemmas 1 and 2, Theorem 2 and Corollary 1, <https://doi.org/10.48550/arXiv.2110.13787>.
