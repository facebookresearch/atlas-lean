# Completeness forces respondents at every outcome value

Let $\mathcal{Y}$ and $\mathcal{Z}$ be finite sets and let $P$ be a finite measure on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$ with coordinates $R$, $Y$, $Z$; write $p(r, y, z) = P(\{(r, y, z)\})$. Suppose $P$ is complete: every $g : \mathcal{Y} \to \mathbb{R}$ with $\sum_{y} p(\mathrm{true}, y, z)\, g(y) = 0$ for all $z$ is identically $0$. Then for every $y \in \mathcal{Y}$,

$$\sum_{z \in \mathcal{Z}} p(\mathrm{true}, y, z) \neq 0.$$

When the singletons of $\mathcal{Y}$ and $\mathcal{Z}$ are measurable, this sum is $P(R = \mathrm{true}, Y = y)$, so every outcome value has respondents. Without measurable singletons the singleton masses are outer measures and their sum need not be that probability.
