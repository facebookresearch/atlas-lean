# Prior reweighting of single-effect fine-mapping posteriors

In the sum-of-single-effects model for $m$ variants in a locus, the effect vector is $b = \sum_{l=1}^{L} b_l$ with each $b_l$ having exactly one nonzero entry. Fitting under a uniform prior returns, for each effect $l$, a probability vector $\alpha_l$ with $\alpha_l(v)$ the posterior probability that effect $l$ sits at variant $v$; credible sets containing a pair of variants with absolute correlation below $0.5$ are discarded as impure. Given positive prior weights $w_1, \dots, w_m$ (for example a predicted probability that each variant modifies expression in the tissue), define

$$\hat\alpha_l(v) = \frac{w_v\,\alpha_l(v)}{\sum_{u=1}^{m} w_u\,\alpha_l(u)}$$

if effect $l$ has a pure credible set, and $\hat\alpha_l = \alpha_l$ otherwise. Updated posterior inclusion probabilities and credible sets follow from the $\hat\alpha_l$ as in the original method, $\mathrm{PIP}(v) = 1 - \prod_{l}\bigl(1 - \hat\alpha_l(v)\bigr)$. The prior may be tempered by capping the ratio of its largest to smallest value (for example at 100).

## Depends on

- [Sum of Single Effects (SuSiE) model and factored variational family](../../sum-of-single-effects-susie/sum-of-single-effects-model.md)

## Expansion

For a single-effect regression with residual data held fixed, the posterior under prior $\pi$ is $\alpha(v) \propto \pi_v\,\mathrm{BF}_v$, where $\mathrm{BF}_v$ is the Bayes factor for variant $v$. Under the uniform prior $\alpha(v) \propto \mathrm{BF}_v$, so multiplying by $w_v$ and renormalizing gives exactly the posterior under the prior $\pi \propto w$. The procedure is approximate only because the full model's coordinate ascent would also refit the other effects' residuals under the new prior; reweighting skips that refit, which keeps the cost negligible at the scale of all genes in 49 tissues. When variants are in perfect LD their Bayes factors are equal and the uniform-prior posterior splits evenly; the prior then decides, which is how functionally informed reweighting resolved 20,913 additional eQTLs to $\mathrm{PIP} > 0.9$.

## Sources

- Q. S. Wang, D. R. Kelley, J. Ulirsch, M. Kanai, et al., "Leveraging supervised learning for functionally informed fine-mapping of cis-eQTLs identifies an additional 20,913 putative causal eQTLs", Nature Communications 12 (2021), Methods ("Approximate functionally informed fine-mapping using EMS") and Results, <https://doi.org/10.1038/s41467-021-23134-8> (PMC8184741).
