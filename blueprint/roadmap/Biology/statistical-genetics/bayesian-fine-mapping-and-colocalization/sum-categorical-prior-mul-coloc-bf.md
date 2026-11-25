# Categorical-prior hypothesis scores equal their closed forms

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants, let $\mathrm{BF}^{(1)}, \mathrm{BF}^{(2)} : \iota \to \mathbb{R}$ be arbitrary, and let $h$ be one of the five [colocalization hypotheses](coloc-hypothesis.md). Then

$$\sum_{S \,:\, H(S) = h} \pi(S)\, \mathrm{BF}(S) = C_{\mathrm{cat}}(h),$$

where the sum runs over the configurations $S \in \iota_\ast \times \iota_\ast$ of [hypothesis](coloc-hypothesis-2.md) $h$, $\pi$ is the [categorical prior](categorical-prior.md), $\mathrm{BF}$ the [configuration Bayes factor](coloc-bf.md) and $C_{\mathrm{cat}}$ the [categorical closed-form score](coloc-categorical-closed-form.md).
