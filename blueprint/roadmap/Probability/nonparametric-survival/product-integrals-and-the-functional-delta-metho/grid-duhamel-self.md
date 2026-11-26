# Two-point grid Duhamel operator on the diagonal

Let $k \in \mathbb{N}$ and index the coordinates of $\mathbb{R}^k$ by $\{0, 1, \dots, k-1\}$. For $x, y \in \mathbb{R}^k$ let $D_{x,y} : \mathbb{R}^k \to \mathbb{R}^k$ be the [two-point Duhamel operator](grid-duhamel.md),

$$
(D_{x,y} h)_j = \sum_{i \le j} \Big(\prod_{l < i} (1 + x_l)\Big)\, h_i \,\Big(\prod_{i < l \le j} (1 + y_l)\Big),
$$

and let $D_x$ be the [Duhamel derivative of the grid product integral](duhamel-deriv.md) at $x$,

$$
(D_x h)_j = \sum_{i \le j} \Big(\prod_{l < i} (1 + x_l)\Big)\, h_i \,\Big(\prod_{i < l \le j} (1 + x_l)\Big),
$$

with empty products equal to $1$. Then for every $x \in \mathbb{R}^k$ the two continuous linear maps coincide: $D_{x,x} = D_x$.

## Sources

- R. D. Gill and S. Johansen, "A survey of product-integration with a view toward application in survival analysis", Ann. Statist. 18 (1990), 1501–1555.
