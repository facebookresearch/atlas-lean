# Existence of optimal chemotherapy and lactate-targeting controls

Let $\Omega \subset \mathbb{R}^d$ ($d = 2,3$) be a bounded smooth domain (the brain), $T > 0$ the treatment horizon and $Q = \Omega \times (0,T)$. The state is the tumor cell density $\varphi \in [0,N]$, the intracellular lactate concentration $\sigma$, the small displacement $\mathbf{u}$ of the viscoelastic tissue, and the damage variable $z \in [0,1]$. Given controls $\boldsymbol{\chi} = (\chi_1,\chi_2)$, where $\chi_1$ is a cytotoxic drug and $\chi_2$ a lactate-targeting drug, the state solves

$$\partial_t \varphi - \Delta \varphi = \big(p(\sigma,z) - \chi_1\big)\varphi\Big(1 - \frac{\varphi}{N}\Big) - \varphi\, g(\sigma,z), \qquad \partial_t \sigma - \Delta \sigma + \frac{k_1(\varphi,z)\sigma}{k_2(\varphi,z) + \sigma} = \chi_2\, S(\varphi,z),$$

$$-\operatorname{div}\big[\mathbb{A}\,\varepsilon(\partial_t \mathbf{u}) + \mathbb{B}(\varphi,z)\,\varepsilon(\mathbf{u})\big] = \mathbf{f}, \qquad \partial_t z - \Delta z + \beta(z) + \pi(z) \ni \iota - \Psi(\varphi, \varepsilon(\mathbf{u})),$$

with homogeneous Neumann conditions for $\varphi, z$, the Robin condition $\partial_\nu \sigma = \sigma_\Gamma - \sigma$, $\mathbf{u} = 0$ on $\partial\Omega$, and given initial data. Here $\beta$ is a maximal monotone graph forcing $z \in [0,1)$ and $\pi$ a Lipschitz perturbation.

**Hypotheses** (the source's (H1)–(H12)):

- (H1) $p, g \in C^{0,1}(\mathbb{R}^2) \cap C^2(\mathbb{R}^2)$ with $0 \le p \le p^*$, $0 \le g \le g^*$ for positive constants $p^*, g^*$, and $N > 0$ is a constant;
- (H2) $k_1, k_2, S \in C^{0,1}(\mathbb{R}^2) \cap C^2(\mathbb{R}^2)$ with $0 \le k_1 \le k_1^*$, $0 < k_{2*} \le k_2 \le k_2^*$, $0 \le S \le S^*$ for constants $k_1^*, k_{2*}, k_2^*, S^*$;
- (H3) $\mathbb{A}$ is a constant, symmetric, strictly positive definite fourth-order tensor; $\mathbb{B} \in C^{0,1}(\mathbb{R}) \cap C^2(\mathbb{R})$ is bounded, symmetric and positive definite; $\mathbf{f} \in L^\infty(0,T;L^2(\Omega)^d)$;
- (H4) $\beta = \hat\beta'$ for a lower semicontinuous convex $\hat\beta : \mathbb{R} \to [0,+\infty]$ with $\hat\beta \in C^3(0,1)$, $\lim_{r\to0^+}\beta(r) = -\infty$ and $\lim_{r\to1^-}\beta(r) = +\infty$;
- (H5) $\pi = \hat\pi'$ for a concave $\hat\pi \in C^1(\mathbb{R}) \cap C^3(0,1)$, with $\pi$ Lipschitz continuous (the prototype is $\hat\beta(r) + \hat\pi(r) = C_1\big(r\ln r + (1-r)\ln(1-r)\big) - C_2r^2$);
- (H6) $\iota \in L^\infty(Q) \cap H^1(0,T;L^2(\Omega))$;
- (H7) $\Psi \in W^{2,\infty}(\Omega \times \mathbb{R} \times \mathbb{R}^{d\times d})$ (in particular bounded), Lipschitz continuous in $(\varphi,\varepsilon)$ uniformly in $x$;
- (H8) $\sigma_\Gamma \in L^2(0,T;L^2(\partial\Omega))$ with $0 \le \sigma_\Gamma \le M_0$ for a constant $M_0 > 0$;
- (H9) $\varphi_0 \in H^2(\Omega)$ with $\partial_\nu\varphi_0 = 0$ and $0 \le \varphi_0 \le N$; $\sigma_0 \in L^2(\Omega)$ with $0 \le \sigma_0 \le M_0$; $\mathbf{u}_0 \in H^2(\Omega)^d \cap H^1_0(\Omega)^d$; $z_0 \in H^2(\Omega)$ with $\partial_\nu z_0 = 0$, $\operatorname{ess\,inf} z_0 > 0$ and $\operatorname{ess\,sup} z_0 < 1$;
- (H10)–(H12) the weights $\alpha_1, \dots, \alpha_9$ below are non-negative and not all zero, the targets satisfy $\varphi_Q, \sigma_Q, z_Q \in L^2(Q)$, $\varphi_\Omega, \sigma_\Omega \in L^2(\Omega)$, and $\gamma : \Omega \times \mathbb{R} \to [0,\infty)$ is Carathéodory with $\gamma(x,\cdot) \in C^1(\mathbb{R})$ and $|\gamma| + |\partial_\varphi\gamma| \le C_\gamma$ on $\Omega \times [0,N]$.

The admissible set is $\mathcal{U}_{ad} = \mathcal{U}^1_{ad} \times \mathcal{U}^2_{ad}$ with

$$\mathcal{U}^1_{ad} = \{\chi_1 \in L^2(0,T;H^1(\Omega)) \cap L^\infty(Q) : \|\chi_1\|_{L^2(H^1)} \le C_{ad},\ \underline{\chi}_1 \le \chi_1 \le \overline{\chi}_1\}, \qquad \mathcal{U}^2_{ad} = \{\chi_2 \in L^\infty(Q) : \underline{\chi}_2 \le \chi_2 \le \overline{\chi}_2\},$$

a nonempty closed convex set. The cost is the tracking-type functional

$$\mathcal{J} = \tfrac{\alpha_1}{2}\|\varphi - \varphi_Q\|^2_{L^2(Q)} + \tfrac{\alpha_2}{2}\|\varphi(T) - \varphi_\Omega\|^2_{L^2(\Omega)} + \alpha_3 \int_\Omega \varphi(T) + \tfrac{\alpha_4}{2}\|\sigma - \sigma_Q\|^2_{L^2(Q)} + \tfrac{\alpha_5}{2}\|\sigma(T) - \sigma_\Omega\|^2_{L^2(\Omega)} + \tfrac{\alpha_6}{2}\|\sqrt{\gamma(\varphi)}\,\varepsilon(\mathbf{u})\|^2_{L^2(Q)} + \tfrac{\alpha_7}{2}\|z - z_Q\|^2_{L^2(Q)} + \alpha_8 \int_\Omega z(T) + \tfrac{\alpha_9}{2}\|\boldsymbol{\chi}\|^2_{L^2(Q)},$$

with non-negative weights not all zero (H10).

**Theorem.**

1. (Well-posedness) For every admissible-type control the state system has a unique weak solution with $0 \le \varphi \le N$, $0 \le \sigma \le M$, $0 < z < 1$, the regularity $\varphi \in H^1(0,T;H^1) \cap L^\infty(0,T;H^2) \cap L^2(0,T;H^3)$, $z \in H^1(0,T;H^1) \cap L^\infty(0,T;H^2)$, and a uniform a-priori bound on bounded sets of controls; the solution depends continuously on the controls.
2. (Separation) On each bounded control set there are constants $0 < r_* \le r^* < 1$ with $r_* \le z \le r^*$ a.e. in $Q$, so the singular graph $\beta$ is never active at the degenerate values.
3. (Existence) The problem $\min_{\boldsymbol{\chi} \in \mathcal{U}_{ad}} \mathcal{J}$ has at least one minimizer $\boldsymbol{\chi}^*$.

## Expansion

The reduced cost is proper and non-negative, so a minimizing sequence exists. It is bounded in $[L^2(H^1) \cap L^\infty] \times L^\infty$, hence weakly-star convergent along a subsequence, and the limit stays in $\mathcal{U}_{ad}$ because a closed convex set is weakly closed. The uniform state estimates together with the Aubin–Lions lemma give strong convergence of the states, enough to pass to the limit in the nonlinear terms, and weak lower semicontinuity of $\mathcal{J}$ shows the limit is optimal. The separation property keeps the damage strictly inside $(0,1)$, which later makes the damage equation differentiable.

## Sources

- Giulia Cavalleri, Alain Miranville, "Optimal control on a brain tumor growth model with lactate metabolism, viscoelastic effects, and tissue damage", Discrete and Continuous Dynamical Systems - B 32 (2026), 219–245, <https://doi.org/10.3934/dcdsb.2025129>. Published version of arXiv:2503.17049, cited next; locators there refer to the arXiv version.
- Giulia Cavalleri, Alain Miranville, "Optimal control on a brain tumor growth model with lactate metabolism, viscoelastic effects, and tissue damage", arXiv (2025). Section 2 (state system), Theorem 2.6, Proposition 2.8, Theorem 3.1. <https://doi.org/10.48550/arXiv.2503.17049>
