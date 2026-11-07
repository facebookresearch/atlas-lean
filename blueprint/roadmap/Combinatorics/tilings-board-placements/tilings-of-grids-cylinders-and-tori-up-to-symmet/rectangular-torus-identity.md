# Torus fixed-tiling sum for the identity

Let $n$ and $m$ be positive integers, let $T$ be
a finite set of tiles and let $\sigma$ be a permutation of $T$ with $\sigma^1 = 1$, that is, the
identity. For $(a, b) \in \mathbb{Z}/n \times \mathbb{Z}/m$ let $N(a, b)$ be the number of tilings
$F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with $F(x + a, y + b) = \sigma(F(x, y))$ for every
cell $(x, y)$. Then, with $\varphi$ Euler's totient function,

$$\sum_{a \in \mathbb{Z}/n} \sum_{b \in \mathbb{Z}/m} N(a, b) =
\sum_{c \mid m} \sum_{d \mid n} \varphi(c) \, \varphi(d) \, |T|^{mn / \operatorname{lcm}(c, d)}.$$

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 34.
