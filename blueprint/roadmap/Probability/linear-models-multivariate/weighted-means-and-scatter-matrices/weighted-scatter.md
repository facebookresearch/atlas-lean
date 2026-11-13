# Weighted scatter matrix

Let $I$ be a finite set and $J$ an index set, let
$x_i \in \mathbb{R}^J$ ($i \in I$) be points with real weights $w_i$, and let
$\mu \in \mathbb{R}^J$. The weighted scatter matrix of the $x_i$ about $\mu$ is the real
$J \times J$ matrix

$$
C = \Big(\sum_{i \in I} w_i\Big)^{-1} \sum_{i \in I} w_i \, (x_i - \mu)(x_i - \mu)^{\mathsf T},
$$

with the convention $0^{-1} = 0$ when the weights sum to $0$. When $\mu$ is the weighted mean of
the $x_i$, it is the weighted sample covariance.
