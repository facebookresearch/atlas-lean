# Point identification under a budget of invalid instruments

**Setting.** Candidate instruments $\mathbf{Z}\in\mathbb{R}^{d_Z}$ (in Mendelian randomization, genetic variants), exposures $\mathbf{X}$ and outcome $Y$ follow the structural equations
$$\mathbf{Z} := f_z(\epsilon_z), \qquad \mathbf{X} := f_x(\mathbf{Z}, \epsilon_x), \qquad Y := \boldsymbol{\theta}^{*}\cdot\boldsymbol{\Phi}(\mathbf{X}) + g_y(\mathbf{Z}, \epsilon_y),$$
with arbitrary latent confounding in the noises and known basis functions $\boldsymbol{\Phi}$ of dimension $d_\Phi \le d_Z$. Let $\boldsymbol\beta_\Phi = \mathrm{Cov}(\boldsymbol\Phi(\mathbf{X}),\mathbf{Z})$, $\boldsymbol\beta_y = \mathrm{Cov}(Y,\mathbf{Z})$ and $\boldsymbol\gamma_g = \mathrm{Cov}(g_y(\mathbf{Z},\epsilon_y),\mathbf{Z})$; the $i$th instrument is valid when $(\gamma_g)_i = 0$. Then $\boldsymbol\gamma_g = \boldsymbol\beta_y - \boldsymbol\theta^{*}\cdot\boldsymbol\beta_\Phi$. Under the relaxed exogeneity assumption $\boldsymbol\gamma_g\in\boldsymbol\Gamma$, the sharp identified set is $\{\boldsymbol\theta : \boldsymbol\beta_y - \boldsymbol\theta\cdot\boldsymbol\beta_\Phi \in \boldsymbol\Gamma\}$.

**Theorem ($L_0$ budget).** Suppose $\operatorname{rank}\boldsymbol\beta_\Phi = d_\Phi$ with every component of $\boldsymbol\beta_\Phi$ nonzero, and at most $b$ instruments are invalid ($\|\boldsymbol\gamma_g\|_0 \le b$). For $b < d_Z - d_\Phi + 1$ the identified set is finite with cardinality
$$t \le \frac{d_Z!}{(d_\Phi-1)!\,(d_Z-d_\Phi+1)!}\left\lfloor \frac{d_Z-d_\Phi+1}{d_Z-b-d_\Phi+1}\right\rfloor,$$
and the bound is attained for some covariances. For a scalar exposure ($d_\Phi = 1$),
$$t \le \left\lfloor \frac{d_Z}{d_Z-b}\right\rfloor \le d_Z,$$
so $\theta^{*}$ is point identified whenever fewer than half the candidate instruments are invalid ($b < d_Z/2$). For $d_\Phi > 1$ no budget $b$ guarantees $t\le 1$.

## Expansion

Each feasible $\boldsymbol\theta$ must make at least $d_Z-b$ coordinates of $\boldsymbol\beta_y - \boldsymbol\theta\cdot\boldsymbol\beta_\Phi$ vanish. For $d_\Phi=1$ the $i$th coordinate vanishes only at the ratio estimate $\theta_i = (\beta_y)_i/(\beta_\Phi)_i$; distinct feasible values need disjoint groups of at least $d_Z-b$ agreeing ratios, so there are at most $\lfloor d_Z/(d_Z-b)\rfloor$ of them, which is the majority-valid rule. In higher dimension each feasible point is determined by $d_\Phi$ of the vanishing coordinates, which yields the binomial factor.

## Sources

- J. Penn, L. M. Gunderson, G. Bravo-Hermsdorff, R. Silva, "BudgetIV: optimal partial identification of causal effects with mostly invalid instruments", arXiv:2411.06913, Lemma 1, Theorems 1–2, Theorem 5 and Corollary 2. <https://doi.org/10.48550/arXiv.2411.06913>
