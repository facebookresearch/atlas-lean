# Explicit formula for an inhomogeneous linear recurrence

Let $k \in \mathbb{N}$ and let
$A, f, G, w \colon \mathbb{N} \to \mathbb{C}$ be sequences such that, for every $m \ge k$,
$f_m = \sum_{i=1}^{k} A_i f_{m-i}$ and $G_m = \sum_{i=1}^{k} A_i G_{m-i} + w_{m-k}$. Suppose
moreover that $f_j = 0$ for every $j < k - 1$ and $f_{k-1} = 1$. Then for every $n \ge k - 1$,

$$G_{n+1} = \sum_{j=0}^{k-1} \sum_{i=0}^{k-1-j} f_{n-j} A_{j+1+i} G_{k-1-i} +
\sum_{j=0}^{n} f_{n-j} w_j.$$

For $k = 0$ the index $k - 1$ is read as $0$, so the hypotheses cannot all hold. The source
states the formula for $n \ge k$, as a consequence of its Theorem 1.

## Sources

- Hacène Belbachir, Fella Rami, and László Szalay, *Alternating Sums in the Generalized Hyperbolic Pascal Triangle*, INTEGERS 24 (2024), Article A84, Corollary 1.
