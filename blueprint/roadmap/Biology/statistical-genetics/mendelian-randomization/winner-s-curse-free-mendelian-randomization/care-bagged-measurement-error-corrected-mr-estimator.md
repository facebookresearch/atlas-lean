# CARE: bagged, measurement-error-corrected MR estimator with invalid-instrument screening

**Model (Assumption 1).** Summary statistics for independent SNPs satisfy

$$\begin{pmatrix}\hat\beta_{Xj}\\ \hat\beta_{Yj}\end{pmatrix}\sim N\!\left(\begin{pmatrix}\beta_{Xj}\\ \theta\beta_{Xj}+r_j\end{pmatrix},\begin{pmatrix}\sigma_{Xj}^2&0\\0&\sigma_{Yj}^2\end{pmatrix}\right),$$

with $\theta$ the causal effect and $r_j=\alpha_j+\beta_{YU}\phi_j$ the total (uncorrelated plus correlated) pleiotropic effect; SNP $j$ is a valid instrument iff $r_j=0$. The variances are of order $1/n$.

**Screening loss.** On a set $\mathcal S$ of relevant SNPs, with $v$ the number of valid instruments,

$$\min_{\theta,(r_j)}\ \sum_{j\in\mathcal S}\frac{(\hat\beta_{Yj}-\theta\hat\beta_{Xj}-r_j)^2}{\sigma_{Yj}^2}-\sum_{j\in\mathcal S}\frac{\theta^2\sigma_{Xj}^2}{\sigma_{Yj}^2}\mathbf 1\{r_j=0\}\quad\text{s.t.}\quad\sum_{j\in\mathcal S}\mathbf 1\{r_j=0\}=v .$$

The second term corrects for measurement error in $\hat\beta_{Xj}$: on the true valid set the profiled loss is unbiased for the weighted least-squares loss with the true $\beta_{Xj}$. The $\ell_0$ constraint is solved by block coordinate descent with monotone decrease of the objective, and $v$ is chosen by the generalized BIC $-2\hat l+\log(n)(s-v)$, whose penalty grows faster than $\log s_\lambda$.

**Estimator.** Use randomized instrument selection $\mathcal S_\lambda$ with Rao–Blackwellized $\hat\beta_{Xj,RB}$ and $\hat\sigma^2_{Xj,RB}$ in place of $\hat\beta_{Xj}$ and $\sigma^2_{Xj}$. Draw $B$ bootstrap samples of $\mathcal S_\lambda$ with multiplicities $w^*_{jb}$, screen invalid SNPs in each to get $\hat{\mathcal V}_b$, refit, and average:

$$\hat\theta_b=\frac{\sum_{j\in\hat{\mathcal V}_b}\hat\beta_{Yj}\hat\beta_{Xj,RB}/\sigma_{Yj}^2}{\sum_{j\in\hat{\mathcal V}_b}\bigl(\hat\beta_{Xj,RB}^2-\hat\sigma^2_{Xj,RB}\bigr)/\sigma_{Yj}^2},\qquad\tilde\theta=\frac1B\sum_{b=1}^B\hat\theta_b .$$

The variance is estimated by the nonparametric delta method, $\hat\sigma_n^2=\sum_{j\in\mathcal S_\lambda}\hat S_j^2$ with $\hat S_j=\frac1B\sum_b(w^*_{jb}-\bar w^*_j)(\hat\theta_b-\tilde\theta)$, giving the interval $\tilde\theta\pm z_{\alpha/2}\hat\sigma_n$.

**Theorem (asymptotic normality).** Let $\kappa_\lambda=s_\lambda^{-1}\sum_{j\in\mathcal S_\lambda}\beta_{Xj}^2/\sigma_{Yj}^2$ be the average selected instrument strength. Assume Assumption 1, a variance-stabilization condition with no dominating instrument ($\max_j\beta_{Xj}^2/\sum_j\beta_{Xj}^2\to_p0$), negligible bias from imperfectly screened invalid instruments after bagging, and pseudo-noise scales bounded and bounded away from zero. If $s_\lambda\to_p\infty$ and $\kappa_\lambda\lambda^2\to_p\infty$, then $\tilde\theta-\theta$ admits, after scaling, an asymptotically linear representation in

$$\tilde u_j=\hat\beta_{Xj,RB}(\theta\beta_{Xj}+v_j)-\theta\bigl(\hat\beta_{Xj,RB}^2-\hat\sigma^2_{Xj,RB}\bigr),\qquad j\in\mathcal S_\lambda,$$

and conditional on the selection event $\tilde\sigma^{-1}(\tilde\theta-\theta)\rightsquigarrow N(0,1)$ with $\tilde\sigma^2=\sum_{j\in\mathcal S_\lambda}\tau_j^2\,\mathrm{Var}(\tilde u_j\mid\mathcal S_\lambda)/a_\lambda^2$, where $a_\lambda$ and $\tau_j$ are the variance-stabilizing quantities of the second assumption.

## Expansion

Each $\hat\theta_b$ is a debiased inverse-variance-weighted estimator: subtracting $\hat\sigma^2_{Xj,RB}$ in the denominator removes the regression-dilution bias that $E\hat\beta_{Xj}^2=\beta_{Xj}^2+\sigma_{Xj}^2$ would otherwise cause, and the Rao–Blackwellized inputs remove the winner's curse. Perfect screening is not needed: the bias condition holds if instruments with large $|r_j|$ are removed, even when some weakly pleiotropic ones remain. The condition $\kappa_\lambda\lambda^2\to\infty$ says the selected instruments are strong on average relative to the threshold.

## Depends on

- [Inverse-variance-weighted estimator](../ivw.md)
- [Rao–Blackwellized exposure effect under randomized instrument selection](rao-blackwellized-exposure-effect-under-randomized-instrument-selection.md)

## Sources

- Z. Xie, W. Zhang, J. Wang, C. Wu, "Winner's Curse Free Robust Mendelian Randomization with Summary Data", *Journal of the American Statistical Association* (2026), Assumptions 1–4, Equations (3)–(5), the GBIC of Section 3.1, Section 3.3 (bootstrap aggregation and inference) and Theorem 1 of Section 4, <https://doi.org/10.1080/01621459.2025.2587321>, PMCID PMC13004071.
