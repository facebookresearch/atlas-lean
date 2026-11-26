# Coordinates of the two-point grid Duhamel operator

Let $k \in \mathbb{N}$ and index the coordinates of $\mathbb{R}^k$ by $\{0, 1, \dots, k-1\}$. For $x, y \in \mathbb{R}^k$, the [two-point Duhamel operator](grid-duhamel.md) is a continuous linear map $D_{x,y} : \mathbb{R}^k \to \mathbb{R}^k$. For every $h \in \mathbb{R}^k$ and every index $j$,

$$
(D_{x,y} h)_j = \sum_{i \le j} \Big(\prod_{l < i} (1 + x_l)\Big)\, h_i \,\Big(\prod_{i < l \le j} (1 + y_l)\Big),
$$

where an empty product equals $1$.

## Sources

- R. D. Gill and S. Johansen, "A survey of product-integration with a view toward application in survival analysis", Ann. Statist. 18 (1990), 1501–1555.
