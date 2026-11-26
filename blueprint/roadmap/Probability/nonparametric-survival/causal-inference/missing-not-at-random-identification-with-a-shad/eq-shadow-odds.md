# Uniqueness of the odds

Let $\mathcal{Y}$ and $\mathcal{Z}$ be finite sets with measurable singletons, and let $P$ be a finite measure on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$, whose coordinates are the response indicator $R$, the outcome $Y$ and the shadow variable $Z$. Write $p(r, y, z) = P(\{(r, y, z)\})$ for the point masses. Suppose $P$ satisfies the shadow assumption: for every measurable $B \subseteq \mathcal{Z}$ and every $y$, $P(R = \mathrm{true}, Z \in B, Y = y)\, P(Y = y) = P(R = \mathrm{true}, Y = y)\, P(Z \in B, Y = y)$, and $P$ is complete: every $g : \mathcal{Y} \to \mathbb{R}$ with $\sum_{y} p(\mathrm{true}, y, z)\, g(y) = 0$ for all $z$ is identically $0$. If $g : \mathcal{Y} \to \mathbb{R}$ satisfies

$$\sum_{y \in \mathcal{Y}} g(y)\, p(\mathrm{true}, y, z) = \sum_{y \in \mathcal{Y}} p(\mathrm{false}, y, z) \quad \text{for every } z \in \mathcal{Z},$$

then $g(y) = \sum_{z} p(\mathrm{false}, y, z) / \sum_{z} p(\mathrm{true}, y, z)$ for every $y$, that is, $g$ equals the nonresponse odds.
