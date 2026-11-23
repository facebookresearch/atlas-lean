# The coloc closed forms

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants, let $\mathrm{BF}^{(1)}, \mathrm{BF}^{(2)} : \iota \to \mathbb{R}$ be arbitrary, and let $h$ be one of the five [colocalization hypotheses](coloc-hypothesis.md). Then (Giambartolomei et al. 2014)

$$\sum_{S \,:\, H(S) = h} w(S)\, \mathrm{BF}(S) = C(h),$$

where the sum runs over the configurations $S \in \iota_\ast \times \iota_\ast$ of [hypothesis](coloc-hypothesis-2.md) $h$, $w$ is the [unnormalized configuration weight](weight.md), $\mathrm{BF}$ the [configuration Bayes factor](coloc-bf.md) and $C$ the [closed-form score](coloc-closed-form.md).

## Sources

- C. Giambartolomei et al., *Bayesian test for colocalisation between pairs of genetic association studies using summary statistics*, PLoS Genet. 10 (2014), e1004383.
