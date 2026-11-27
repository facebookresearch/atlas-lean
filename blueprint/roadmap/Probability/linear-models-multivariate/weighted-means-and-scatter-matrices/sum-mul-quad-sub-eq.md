# The bias-variance split of a weighted quadratic form

Let $I$ and $J$ be finite sets, let
$x_i \in \mathbb{R}^J$ ($i \in I$) be points with real weights $w_i$ such that $\sum_i w_i \ne 0$,
let $m$ be their weighted mean, let $A$ be a symmetric real $J \times J$ matrix, and let
$\mu \in \mathbb{R}^J$. Then

$$
\sum_{i \in I} w_i \, (x_i - \mu)^{\mathsf T} A \, (x_i - \mu) =
\sum_{i \in I} w_i \, (x_i - m)^{\mathsf T} A \, (x_i - m) +
\Big(\sum_{i \in I} w_i\Big) (m - \mu)^{\mathsf T} A \, (m - \mu).
$$
