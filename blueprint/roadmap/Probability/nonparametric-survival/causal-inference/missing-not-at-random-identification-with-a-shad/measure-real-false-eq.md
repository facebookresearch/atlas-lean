# Measure Real false eq

Let $\mathcal{Y}$ and $\mathcal{Z}$ be finite sets with measurable singletons, and let $P$ be a finite measure on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$, whose coordinates are the response indicator $R$, the outcome $Y$ and the shadow variable $Z$. Write $p(r, y, z) = P(\{(r, y, z)\})$ for the point masses. Suppose $P$ satisfies the shadow assumption: for every measurable $B \subseteq \mathcal{Z}$ and every $y$, $P(R = \mathrm{true}, Z \in B, Y = y)\, P(Y = y) = P(R = \mathrm{true}, Y = y)\, P(Z \in B, Y = y)$. Let $y \in \mathcal{Y}$ with $\sum_{z} p(\mathrm{true}, y, z) \neq 0$, and let $a(y) = \sum_{z} p(\mathrm{false}, y, z) / \sum_{z} p(\mathrm{true}, y, z)$ be the nonresponse odds. Then for every $z \in \mathcal{Z}$,

$$p(\mathrm{false}, y, z) = a(y)\, p(\mathrm{true}, y, z).$$
