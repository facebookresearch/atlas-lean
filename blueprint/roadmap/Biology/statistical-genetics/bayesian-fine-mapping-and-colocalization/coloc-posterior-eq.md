# Colocalization normalization identity

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants, let $\mathrm{BF}^{(1)}, \mathrm{BF}^{(2)} : \iota \to \mathbb{R}$ be arbitrary, and let $h$ be one of the five [colocalization hypotheses](coloc-hypothesis.md). Then

$$\frac{\sum_{S \,:\, H(S) = h} w(S)\, \mathrm{BF}(S)}{\sum_{S} w(S)\, \mathrm{BF}(S)} = \frac{C(h)}{\sum_{h'} C(h')},$$

with the convention $x / 0 = 0$, where $S$ ranges over configurations in $\iota_\ast \times \iota_\ast$, $h'$ over the five hypotheses, $w$ is the [unnormalized configuration weight](weight.md), $\mathrm{BF}$ the [configuration Bayes factor](coloc-bf.md) and $C$ the [closed-form score](coloc-closed-form.md). For arbitrary real Bayes factors these ratios need not be probabilities.
