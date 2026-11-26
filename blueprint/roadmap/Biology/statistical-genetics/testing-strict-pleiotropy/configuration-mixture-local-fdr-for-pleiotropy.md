# Configuration-mixture local FDR for pleiotropy

For variant $j$ and trait $k$, model the Wald score by the two-group scale mixture

$$W_{jk} \sim (1 - p_k)\,N(0,1) + p_k\,N(0,\sigma_k^2), \qquad \sigma_k^2 > 1,$$

and let $\mathbf{Z}_j \in \{0,1\}^K$ indicate the traits with nonzero effect, with configuration probabilities $\pi_{\mathbf z}$ and $|\mathbf z| = \sum_k z_k$. The pair covariance of scores is $\rho^e_{kk'}$ (estimation-error correlation from sample overlap) when the variant affects at most one of the two traits, and $\sqrt{(\sigma_k^2 - 1)(\sigma_{k'}^2 - 1)}\,\rho^b_{kk'} + \rho^e_{kk'}$ when it affects both ($\rho^b$ the genetic correlation of effects). With $\Sigma(\mathbf z)$ the resulting $K\times K$ covariance and $\phi_K$ the centered Gaussian density, the local false discovery rate for the composite null $H_0^r$ (at most $r-1$ affected traits) is

$$\mathrm{lfdr}(\mathbf W_j) = P(H_0^r \mid \mathbf W_j) = \frac{\sum_{\mathbf z:|\mathbf z| \le r-1}\pi_{\mathbf z}\,\phi_K(\mathbf W_j;\Sigma(\mathbf z))}{\sum_{\mathbf z}\pi_{\mathbf z}\,\phi_K(\mathbf W_j;\Sigma(\mathbf z))}.$$

Parameters are fitted by EM on a penalized complete log-likelihood whose penalty $\lambda\sum \pi_{\mathbf z_1}/\pi_{\mathbf z_2}$ runs over configuration pairs differing in one trait ($\mathbf z_1$ having the extra trait), discouraging larger configurations from receiving more mass than their sub-configurations; variants are then rejected by thresholding lfdr to control FDR.

## Depends on

- [Minimum-Wald intersection–union test for strict pleiotropy](minimum-wald-intersection-union-test-for-strict-pleiotropy.md)

## Expansion

Modeling the variance rather than the mean of non-null scores keeps one scale parameter per trait, so the parameter count grows with the $2^K$ configuration weights and $O(K^2)$ correlations only. Under the posterior, rejecting variants in increasing order of lfdr while the running mean of lfdr stays below the target level controls the Bayesian FDR. Without the penalty, an overestimated weight for a large configuration can make a variant with stronger evidence for a smaller configuration look more pleiotropic, producing non-monotone decisions.

## Sources

- Eva Biswas, Nilanjan Chatterjee and Zheyu Wang, *Testing Procedures for Strict Pleiotropy in Genetic Association Studies*, arXiv:2610.00962 (2026). <https://doi.org/10.48550/arXiv.2610.00962> Section 3 (two-group mixture, covariance structure, composite-null lfdr and penalized EM likelihood).
