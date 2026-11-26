# Summary-data MR adaptive lasso with bootstrap-smoothed inference

**Setting.** Two-sample summary-data Mendelian randomization with $J$ independent (LD-pruned) variants: $\hat\beta_{Xj}\sim N(\beta_{Xj},\sigma^2_{Xj})$ and $\hat\beta_{Yj}\sim N(\beta_{Yj},\sigma^2_{Yj})$ from non-overlapping exposure and outcome GWAS of sizes $n_X,n_Y$, with $\beta_{Yj}=\theta\beta_{Xj}+\alpha_j$, where $\alpha_j$ is the direct (pleiotropic) effect of variant $j$. Let $\mathcal A=\{j:\alpha_j\ne0\}$ be the invalid instruments.

**Estimator (MR-ALasso).** With $\mathbf S=\mathrm{diag}(\tilde w_1,\dots,\tilde w_J)$ inverse-variance weights, the median ratio estimate $\tilde\theta=\mathrm{median}_j\{\hat\beta_{Yj}/\hat\beta_{Xj}\}$, preliminary direct effects $\tilde\alpha_j=\hat\beta_{Yj}-\tilde\theta\hat\beta_{Xj}$ and adaptive weights $\omega_j=|\tilde\alpha_j|^{-\nu}$ ($\nu>0$),

$$(\hat\theta_{AL},\hat{\boldsymbol\alpha}_{AL})=\arg\min_{\theta,\boldsymbol\alpha}\ \tfrac12(\hat{\boldsymbol\beta}_Y-\theta\hat{\boldsymbol\beta}_X-\boldsymbol\alpha)^\top\mathbf S(\hat{\boldsymbol\beta}_Y-\theta\hat{\boldsymbol\beta}_X-\boldsymbol\alpha)+\lambda_n\sum_{j=1}^J\omega_j|\alpha_j| .$$

Profiling out the unpenalized $\theta$ leaves a weighted lasso in $\boldsymbol\alpha$ with Gram matrix $\hat{\mathbf C}_n=\mathbf S-\mathbf S\hat{\boldsymbol\beta}_X(\hat{\boldsymbol\beta}_X^\top\mathbf S\hat{\boldsymbol\beta}_X)^{-1}\hat{\boldsymbol\beta}_X^\top\mathbf S$.

**Theorem.** Let $n=n_Y$, $n_X/n_Y\to\kappa\in(0,\infty)$, fewer than half the variants invalid ($|\mathcal A|<J/2$), $\min_{j\in\mathcal A}|\alpha_j|\ge c_\alpha>0$, $\min_j|\beta_{Xj}|\ge c_X>0$, $\sqrt n(\tilde\theta-\theta)=O_p(1)$, and $n^{-1}\hat{\mathbf C}_n\to\mathbf C$ with $\mathbf C_{\mathcal A\mathcal A}$ positive definite. If

$$\lambda_n=o(\sqrt n),\qquad n^{(\nu-1)/2}\lambda_n\to\infty ,$$

then $P(\hat{\mathcal A}_n=\mathcal A)\to1$ for $\hat{\mathcal A}_n=\{j:\hat\alpha_{AL,j}\ne0\}$, and the post-selection IVW estimator on $\hat{\mathcal V}_n=\hat{\mathcal A}_n^c$ equals the oracle IVW estimator on the true valid set with probability tending to one.

**Bootstrap smoothing.** Resample variants with multinomial counts $\mathbf W^*\sim\mathrm{Multinomial}(J;p)$, refit, and average the estimate over resamples in a stability region $\mathcal R$ (e.g. resamples whose selected valid set is admissible), $S_{\mathcal R}(p)=\mathbb E_p[\hat\theta(\mathbf W^*)\mid\mathbf W^*\in\mathcal R]$. At $p_0=(1/J,\dots,1/J)$ its nonparametric delta-method variance is

$$\sum_{j=1}^J(S_j^*)^2,\qquad S_j^*=\operatorname{Cov}_{p_0}\bigl[W_j^*,\hat\theta(\mathbf W^*)\mid\mathcal R\bigr],$$

and the Monte Carlo covariances from $B$ resamples converge to $S_j^*$ as $B\to\infty$, giving smooth standard errors and intervals that do not condition on a single, discontinuous selection event.

## Expansion

Because $\tilde\theta$ is $\sqrt n$-consistent under the majority-valid rule, $\tilde\alpha_j=O_p(n^{-1/2})$ for valid and $\tilde\alpha_j\to\alpha_j\ne0$ for invalid variants, so the weights diverge like $n^{\nu/2}$ on valid variants and stay bounded on invalid ones. The tuning conditions make the penalty negligible for invalid variants ($\lambda_n/\sqrt n\to0$) and dominant for valid ones ($\lambda_n n^{\nu/2}/\sqrt n\to\infty$), which is Zou's oracle argument applied to the profiled problem; unlike the plain MR-Lasso it needs no irrepresentability condition. The smoothing variance is Efron's bootstrap-after-selection formula, restricted to the conditioning region.

## Depends on

- [Inverse-variance weighted estimator](../mendelian-randomization/ivw.md)

## Sources

- M. Qasim, K. Wang, I. S. Bhatt, "Adaptive Penalization and Bootstrap-Smoothed Inference for Two-Sample Mendelian Randomization with Summary Data", arXiv:2607.18503 (2026), Section 3 (Assumptions on summary data and pleiotropy, Theorem 3.1, Proposition 3.1, Corollary 3.1, Theorem 3.2 and Proposition 3.2). <https://doi.org/10.48550/arXiv.2607.18503>
