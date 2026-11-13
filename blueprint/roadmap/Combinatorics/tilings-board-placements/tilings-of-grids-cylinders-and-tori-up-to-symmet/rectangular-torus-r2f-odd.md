# Fixed points of $r^2 f$ on the rectangular torus, $m$ odd

Let $T$ be a finite set of
tile designs, $\sigma$ a permutation of $T$ with $\sigma^2 = 1$, $n$ a positive integer and $m$ a
positive odd integer. For a shift $(a, b) \in \mathbb{Z}/n \times \mathbb{Z}/m$, count the maps
$F : \mathbb{Z}/n \times \mathbb{Z}/m \to T$ with $F(x+a, -1-y-b) = \sigma(F(x, y))$ for all
cells $(x, y)$, and let $\mathrm{fxpt}$ be the sum of these counts over all $nm$ shifts (the
torus fixed-point count of the reflection $r^2 f$). Write $t_{\mathrm{id}} = |T|$, let
$t_{(r^2f)^d}$ be the number of designs $e \in T$ with $\sigma^d(e) = e$, and let $\varphi$ be
Euler's totient function. Then, with $d$ running over the positive divisors of $n$,

$$\mathrm{fxpt} = m \sum_{d \mid n} \varphi(d)\,
t_{\mathrm{id}}^{n(m-1)/\operatorname{lcm}(d,2)}\,t_{(r^2f)^d}^{n/d}.$$

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 36.
