# Identification by inverse-response weighting under MAR

Let $\mu$ be a probability measure, $R$ a measurable response event, $X$ a measurable covariate taking values in a finite set with measurable singletons, and $Y$ a measurable, integrable real outcome. Write $\pi(x) = P(R \cap \{X = x\}) / P(X = x)$ for the response probability. Suppose the outcome is missing at random given $X$, that is $P(R \cap \{Y \in B\} \cap \{X = x\})\,P(X = x) = P(R \cap \{X = x\})\,P(\{Y \in B\} \cap \{X = x\})$ for every measurable $B$ and every $x$, and that the response is positive: there is $\varepsilon > 0$ with $\pi(x) \ge \varepsilon$ for every $x$ with $P(X = x) > 0$. Then the inverse-response-weighted mean equals the full-data mean:

$$\mathbb E\bigl[\mathbf 1_R\, Y / \pi(X)\bigr] = \mathbb E[Y].$$
