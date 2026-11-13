# Torus fixed-tiling sum for the reflection $f$, $n$ odd

Let $n$ and $m$ be positive
integers with $n$ odd, let $T$ be a finite set of tiles, let $\sigma$ be a permutation of $T$ with
$\sigma^2 = 1$, and for $k \ge 0$ let $t_k$ be the number of tiles $d \in T$ with
$\sigma^k(d) = d$. Let $f(x, y) = (-1 - x, y)$ on $\mathbb{Z}/n \times \mathbb{Z}/m$, and for
$(a, b) \in \mathbb{Z}/n \times \mathbb{Z}/m$ let $N(a, b)$ be the number of tilings
$F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with $F(f(x + a, y + b)) = \sigma(F(x, y))$ for every
cell $(x, y)$. Then, with $\varphi$ Euler's totient function,

$$\sum_{a \in \mathbb{Z}/n} \sum_{b \in \mathbb{Z}/m} N(a, b) =
n \sum_{c \mid m} \varphi(c) \, |T|^{(n-1)m / \operatorname{lcm}(2, c)} \, t_c^{m/c}.$$

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 36.
