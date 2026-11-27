# Feedback over a disjoint union in two steps

In the category of sets and relations with the disjoint union as tensor, let $f : X \sqcup (U \sqcup V) \to Y \sqcup (U \sqcup V)$ be a relation, and write $\mathrm{fb}$ for [feedback](feedback.md). With the associators $\alpha_X : (X \sqcup U) \sqcup V \to X \sqcup (U \sqcup V)$ and $\alpha_Y$ likewise,

$$\mathrm{fb}_{U \sqcup V}(f) = \mathrm{fb}_U\bigl(\mathrm{fb}_V(\alpha_X ; f ; \alpha_Y^{-1})\bigr),$$

where $;$ is composition in forward order: feeding back $V$ first, after reassociating, and then $U$ gives the feedback over the disjoint union.
