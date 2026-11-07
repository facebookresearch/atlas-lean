# Square-torus fixed points of the reflection $f$, odd $n$

Let $n$ be an odd positive
integer, let $T$ be a finite set of tile designs, and let $\sigma$ be a permutation of $T$ with
$\sigma^2 = 1$. For $k \ge 1$ let $t_k$ be the number of designs in $T$ fixed by $\sigma^k$. Let
$f$ be the cell map $(x, y) \mapsto (-1-x, y)$ of $(\mathbb{Z}/n\mathbb{Z})^2$, and let $S$ be the
sum, over all shifts $v \in (\mathbb{Z}/n\mathbb{Z})^2$, of the number of tilings
$F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$ with $F(f(c + v)) = \sigma(F(c))$ for every cell $c$.
Writing $\varphi$ for Euler's totient function,

$$S = n \sum_{d \mid n} \varphi(d) \, |T|^{(n^2-n)/\operatorname{lcm}(2, d)} \, t_d^{n/d},$$

where $d$ runs over the positive divisors of $n$.

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 38.
