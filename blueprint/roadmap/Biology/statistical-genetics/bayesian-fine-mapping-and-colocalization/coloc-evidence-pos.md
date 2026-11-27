# Positivity of colocalization evidence

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants, and let $\mathrm{BF}^{(1)}, \mathrm{BF}^{(2)} : \iota \to \mathbb{R}$ satisfy $\mathrm{BF}^{(1)}_j \ge 0$ and $\mathrm{BF}^{(2)}_j \ge 0$ for every $j$. Then the total of the [closed-form scores](coloc-closed-form.md) over the five hypotheses is strictly positive:

$$\sum_{h \in \{H_0, \dots, H_4\}} C(h) > 0.$$

This holds because $C(H_0) = 1$ and the other scores are nonnegative.
