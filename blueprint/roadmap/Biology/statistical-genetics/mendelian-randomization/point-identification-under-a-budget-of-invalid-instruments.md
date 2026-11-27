# Point identification under a budget of invalid instruments

**Setting.** Candidate instruments $\mathbf{Z}\in\mathbb{R}^{d_Z}$ (in Mendelian randomization, genetic variants), exposures $\mathbf{X}$ and outcome $Y$ follow the structural equations

$$\mathbf{Z} := f_z(\epsilon_z), \qquad \mathbf{X} := f_x(\mathbf{Z}, \epsilon_x), \qquad Y := \boldsymbol{\theta}^{*}\cdot\boldsymbol{\Phi}(\mathbf{X}) + g_y(\mathbf{Z}, \epsilon_y),$$

with arbitrary latent confounding in the noises and known basis functions $\boldsymbol{\Phi}$ of dimension $d_\Phi \le d_Z$. Let $\boldsymbol\beta_\Phi = \mathrm{Cov}(\boldsymbol\Phi(\mathbf{X}),\mathbf{Z})$, $\boldsymbol\beta_y = \mathrm{Cov}(Y,\mathbf{Z})$ and $\boldsymbol\gamma_g = \mathrm{Cov}(g_y(\mathbf{Z},\epsilon_y),\mathbf{Z})$; the $i$th instrument is valid when $(\gamma_g)_i = 0$. Then $\boldsymbol\gamma_g = \boldsymbol\beta_y - \boldsymbol\theta^{*}\cdot\boldsymbol\beta_\Phi$. Under the relaxed exogeneity assumption $\boldsymbol\gamma_g\in\boldsymbol\Gamma$, the sharp identified set is $\{\boldsymbol\theta : \boldsymbol\beta_y - \boldsymbol\theta\cdot\boldsymbol\beta_\Phi \in \boldsymbol\Gamma\}$.

**Theorem ($L_0$ budget).** Suppose $\operatorname{rank}\boldsymbol\beta_\Phi = d_\Phi$ with $(\boldsymbol\beta_\Phi)_i = \mathrm{Cov}(\boldsymbol\Phi(\mathbf{X}), Z_i) \ne 0$ for every $i$, and at most $b$ instruments are invalid ($\|\boldsymbol\gamma_g\|_0 \le b$). If $b = 0$, the identified set is $\{\boldsymbol\theta^{*}\}$: $\boldsymbol\theta^{*}$ is the unique solution of $\boldsymbol\beta_y = \boldsymbol\theta\cdot\boldsymbol\beta_\Phi$. For $b < d_Z - d_\Phi + 1$, one of two cases holds: (i) the identified set is unbounded in some but not all directions; or (ii) it is finite with cardinality

$$t \le \frac{d_Z!}{(d_\Phi-1)!\,(d_Z-d_\Phi+1)!}\left\lfloor \frac{d_Z-d_\Phi+1}{d_Z-b-d_\Phi+1}\right\rfloor,$$

and the bound is attained for some covariances. Case (i) can occur only when $d_\Phi > 1$, because full rank of $\boldsymbol\beta_\Phi$ does not make every $d_\Phi$ of its columns linearly independent. For a scalar exposure ($d_\Phi = 1$),

$$t \le \left\lfloor \frac{d_Z}{d_Z-b}\right\rfloor \le d_Z,$$

so $\theta^{*}$ is point identified whenever fewer than half the candidate instruments are invalid ($b < d_Z/2$).

## Proof depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)

## Proof idea

Each feasible $\boldsymbol\theta$ must make at least $d_Z-b$ coordinates of $\boldsymbol\beta_y - \boldsymbol\theta\cdot\boldsymbol\beta_\Phi$ vanish. For $d_\Phi=1$ the $i$th coordinate vanishes only at the ratio estimate $\theta_i = (\beta_y)_i/(\beta_\Phi)_i$; distinct feasible values need disjoint groups of at least $d_Z-b$ agreeing ratios, so there are at most $\lfloor d_Z/(d_Z-b)\rfloor$ of them, which is the majority-valid rule. In higher dimension each feasible point is determined by $d_\Phi$ of the vanishing coordinates, which yields the binomial factor.

## Sources

- J. Penn, L. M. Gunderson, G. Bravo-Hermsdorff, R. Silva and D. S. Watson, "BudgetIV: optimal partial identification of causal effects with mostly invalid instruments", Proceedings of the 28th International Conference on Artificial Intelligence and Statistics (AISTATS 2025), PMLR 258 (2025), 2485–2493, <https://proceedings.mlr.press/v258/penn25a.html> (PMLR assigns no DOI): Theorem 1 (point identification with valid instruments), Theorem 2 (sharp identified set), Theorem 3 (cardinality bound) and Corollary 3.2 (scalar exposure). The same numbering is used in arXiv:2411.06913v2, <https://arxiv.org/abs/2411.06913v2>.
- The dichotomy (i)/(ii) as stated in the first version, arXiv:2411.06913v1, <https://arxiv.org/abs/2411.06913v1>, Theorem 5 and Corollary 5.1.
