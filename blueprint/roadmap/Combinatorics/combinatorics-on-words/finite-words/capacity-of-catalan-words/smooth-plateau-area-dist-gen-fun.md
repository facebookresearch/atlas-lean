# Continued fraction for smooth words from $j$ to $j$ by area

Let $t(m, j; q)$ be the area
distribution of the words of length $m$ over $\{1, \dots, j\}$ that begin and end with $j$ and whose
consecutive letters differ by at most $1$. Define power series $K_k$ in $x$ over $\mathbb{Z}[q]$ by
$K_1 = 1 - qx$ and $K_k = 1 - q^k x - q^{2k-1} x^2 / K_{k-1}$ for $k \ge 2$; each $K_k$ has constant
term $1$. Then for every $j \ge 1$, in $\mathbb{Z}[q][[x]]$,

$$\sum_{m \ge 0} t(m, j; q)\, x^m = \frac{q^j x}{K_j}.$$

This is Mansour and Shattuck's Lemma 8: $q^j x / K_j$ is the finite continued fraction
$q^j x / (1 - q^j x - q^{2j-1} x^2 / (1 - q^{j-1} x - \cdots / (1 - q^2 x - q^3 x^2 / (1 - qx))))$,
and for $j = 1$ it is $qx / (1 - qx)$. The term $m = 0$ vanishes.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 8.
