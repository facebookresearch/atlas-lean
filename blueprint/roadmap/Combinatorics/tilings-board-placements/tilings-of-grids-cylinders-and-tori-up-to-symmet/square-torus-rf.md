# Fixed tilings of the square torus under the diagonal reflection

Let $n$ be a positive
integer, $T$ a finite set of tile designs and $\sigma$ a permutation of $T$ with $\sigma^2 = 1$;
write $t_1$ for the number of designs $d \in T$ with $\sigma(d) = d$, and let $\varphi$ be Euler's
totient function. Let $S$ be the torus shift sum of the cell map $g(x, y) = (y, x)$ of $rf$ on
$(\mathbb{Z}/n\mathbb{Z})^2$, that is, the sum over all shifts
$(a, b) \in (\mathbb{Z}/n\mathbb{Z})^2$ of the number of tilings
$F : (\mathbb{Z}/n\mathbb{Z})^2 \to T$ with $F(g(c + (a, b))) = \sigma(F(c))$ for every cell $c$.
Then $S = n \left(\sum_{d \mid n,\ d \text{ odd}} \varphi(d) \, |T|^{(n^2-n)/(2d)} \, t_1^{n/d} +
\sum_{d \mid n,\ d \text{ even}} \varphi(d) \, |T|^{n^2/(2d)}\right)$.

The paper writes this as a single divisor sum with a summand depending on the parity of $d$.

## Sources

- Peter Kagey, William Keehn, *Counting Tilings of the n × m Grid, Cylinder, and Torus*, Journal of Integer Sequences 27 (2024), Article 24.6.1, Theorem 40.
