# Weighted additive character sum over reduced residues

For a positive integer $r$ and an
integer $x$ write $e_r(x) = \exp(2\pi i x / r)$, and let $\mu$ be the Möbius function. For all
natural numbers $n \ge 2$ and $k \ge 1$,

$$\sum_{1 \le b \le n,\ \gcd(b, n) = 1} b \, e_n(-kb)
= -n \sum_{d \mid n,\ (n/d) \nmid k} \frac{\mu(d)}{1 - e_{n/d}(-k)} +
\frac{n}{2} \sum_{d \mid n,\ d < n,\ (n/d) \mid k} \mu(d) \left(\frac{n}{d} - 1\right).$$

## Sources

- O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular Inverse*, INTEGERS 24 (2024), Article A33, Lemma 4.
