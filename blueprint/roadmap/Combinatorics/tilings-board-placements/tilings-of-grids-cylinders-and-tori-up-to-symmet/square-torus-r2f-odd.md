# Fixed tilings of the odd square torus under the reflection $r^2 f$

Let $n$ be an odd
positive integer, $T$ a finite set of tile designs and $\sigma$ a permutation of $T$ with
$\sigma^2 = 1$; for $k \in \mathbb{N}$ write $t_k$ for the number of designs $d \in T$ with
$\sigma^k(d) = d$, and let $\varphi$ be Euler's totient function. Let $S$ be the torus shift sum
of the cell map $g(x, y) = (x, -1-y)$ of $r^2 f$ on $(\mathbb{Z}/n\mathbb{Z})^2$, that is, the
sum over all shifts $(a, b) \in (\mathbb{Z}/n\mathbb{Z})^2$ of the number of tilings
$F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$ with $F(g(c + (a, b))) = \sigma(F(c))$ for every cell $c$.
Then $S = n \sum_{d \mid n} \varphi(d) \, |T|^{(n^2-n)/\operatorname{lcm}(2, d)} \, t_d^{n/d}$.

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 38.
