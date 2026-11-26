# Quadratic form of a weighted scatter matrix

Let $I$ and $J$ be finite sets, let
$x_i \in \mathbb{R}^J$ ($i \in I$) be points with real weights $w_i$, let $\mu \in \mathbb{R}^J$,
and let $C$ be the weighted scatter matrix of the $x_i$ about $\mu$. Then for every
$u \in \mathbb{R}^J$,

$$
u^{\mathsf T} C u =
\Big(\sum_{i \in I} w_i\Big)^{-1} \sum_{i \in I} w_i \big(u \cdot (x_i - \mu)\big)^2,
$$

with the convention $0^{-1} = 0$.
