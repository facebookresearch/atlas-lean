# Converse of the shadow factorization

Let $\mathcal{Y}$ and $\mathcal{Z}$ be finite sets with measurable singletons, and let $P$ be a finite measure on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$, whose coordinates are the response indicator $R$, the outcome $Y$ and the shadow variable $Z$. Write $p(r, y, z) = P(\{(r, y, z)\})$ for the point masses. Suppose there is $b : \mathcal{Y} \to \mathbb{R}$ with

$$p(\mathrm{false}, y, z) = b(y)\, p(\mathrm{true}, y, z) \quad \text{for all } y \in \mathcal{Y},\ z \in \mathcal{Z}.$$

Then $P$ satisfies the shadow assumption: for every measurable $B \subseteq \mathcal{Z}$ and every $y$, $P(R = \mathrm{true}, Z \in B, Y = y)\, P(Y = y) = P(R = \mathrm{true}, Y = y)\, P(Z \in B, Y = y)$.
