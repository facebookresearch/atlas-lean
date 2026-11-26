# Minimum-Wald intersection–union test for strict pleiotropy

For a variant $j$ and $K$ traits, let $\beta_{jk}$ be its per-trait effect in a linear (or logistic) GWAS regression and $W_{jk} = \hat\beta_{jk}/\mathrm{se}(\hat\beta_{jk})$ the published Wald $z$-score. *Strict pleiotropy* is the alternative $H_a^K$: $\beta_{jk} \neq 0$ for every $k$. Its null is the composite union $H_0^K = \bigcup_k\{\beta_{jk} = 0\}$, i.e. the variant affects at most $K-1$ traits. The test statistic is

$$T_{N,j,K} = \min_{k = 1,\dots,K} |W_{jk}|.$$

**Proposition 1.** For $\alpha \in (0,1)$ let $c_\alpha = \Phi^{-1}(1 - \alpha/2)$. Then

$$\lim_{N\to\infty}\ \sup_{\theta \in \Theta_0} P_\theta\big(T_{N,j,K} > c_\alpha\big) = \alpha,$$

where $\theta = (\beta_{j1},\dots,\beta_{jK})$ and $\Theta_0$ is the parameter set of $H_0^K$. The test rejects exactly when every per-trait Wald test rejects at level $\alpha$, requires only summary statistics, and its size does not depend on the correlation among traits or on sample overlap between the GWAS.

**Proposition 2 (likelihood ratio).** With individual-level multivariate Gaussian traits, full design $\mathbf{X}$ and reduced design $\mathbf{X}_r$ (variant column removed), the likelihood-ratio statistic for $H_0^K$ is

$$l_N = \min_{k}\ N\log\Big|1 + \tfrac1N\,\mathbf{Y}_k^\top(\mathbf{P}_{\mathbf{X}} - \mathbf{P}_{\mathbf{X}_r})\mathbf{Y}_k\,(\hat\Sigma^{-1})_{kk}\Big|,$$

with asymptotic level-$\alpha$ rejection region $\{l_N > F^{-1}_{\chi^2_1}(1-\alpha)\}$. Since each per-trait Wald test is asymptotically equivalent to the per-trait LRT, the minimum-Wald test has an asymptotically equivalent rejection region to the LRT.

## Expansion

This is the intersection–union principle: rejecting $\bigcup_k H_{0k}$ requires rejecting every $H_{0k}$, and the supremum of the rejection probability over the null is approached at configurations where exactly one $\beta_{jk} = 0$ and the others are large, so the least favorable size is that of a single marginal test, $\alpha$, with no multiplicity correction across traits. The LRT for a union null also takes the form of a minimum over traits, which is why the minimum statistic is natural rather than ad hoc. The cost is conservativeness when several effects are null at once.

## Sources

- Eva Biswas, Nilanjan Chatterjee and Zheyu Wang, *Testing Procedures for Strict Pleiotropy in Genetic Association Studies*, arXiv:2610.00962 (2026). <https://doi.org/10.48550/arXiv.2610.00962> Section 2.1 (hypotheses), Section 2.2 (Propositions 1 and 2 and the remark on LRT equivalence).
