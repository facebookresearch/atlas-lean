# Posterior identity for the categorical colocalization prior

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants, let $\mathrm{BF}^{(1)}, \mathrm{BF}^{(2)} : \iota \to \mathbb{R}$ be arbitrary, and let $h$ be one of the five [colocalization hypotheses](coloc-hypothesis.md). Then

$$\frac{\sum_{S \,:\, H(S) = h} \pi(S)\, \mathrm{BF}(S)}{\sum_{S} \pi(S)\, \mathrm{BF}(S)} = \frac{C_{\mathrm{cat}}(h)}{\sum_{h'} C_{\mathrm{cat}}(h')},$$

with the convention $x / 0 = 0$, where $S$ ranges over configurations in $\iota_\ast \times \iota_\ast$, $h'$ over the five hypotheses, $\pi$ is the [categorical prior](categorical-prior.md), $\mathrm{BF}$ the [configuration Bayes factor](coloc-bf.md) and $C_{\mathrm{cat}}$ the [categorical closed-form score](coloc-categorical-closed-form.md).
