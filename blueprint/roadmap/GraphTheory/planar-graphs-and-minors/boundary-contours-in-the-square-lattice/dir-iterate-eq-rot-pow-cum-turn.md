# Dart direction after k steps is rotated by the cumulative turn

Let $K \subseteq \mathbb{Z}^2$, let $e$ be any dart of the square lattice and $k$ a natural number. Let $\rho(a, b) = (-b, a)$ be the counterclockwise quarter-turn rotation, $\rho^s$ for $s \in \mathbb{Z}/4\mathbb{Z}$ the rotation by $s$ quarter turns, and $c_k = \sum_{i=0}^{k-1} t_K(\sigma_K^i(e)) \in \mathbb{Z}/4\mathbb{Z}$ the cumulative turn of $e$ over $k$ steps of the boundary successor map $\sigma_K$. Then the direction of $\sigma_K^k(e)$ equals $\rho^{c_k}$ applied to the direction of $e$.
