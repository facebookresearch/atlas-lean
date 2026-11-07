# Continued fraction for the area series of restricted smooth words

For $j \ge 1$, let
$t^*(m, j; q) = \sum_w q^{w_1 + \cdots + w_m}$, the sum over the words $w = w_1 \cdots w_m$ over
$\{1, \dots, j\}$ with $w_1 = w_m = j$ (there are none for $m = 0$), consecutive letters
differing by at most $1$ and no two adjacent letters equal to $1$, and let
$T^*_j(x; q) = \sum_{m \ge 0} t^*(m, j; q)\, x^m$. Define power series $K_k$ in $x$ over
$\mathbb{Z}[q]$ by $K_1 = 1$ and $K_k = 1 - q^k x - q^{2k-1} x^2 / K_{k-1}$ for $k \ge 2$ (each
$K_k$ has constant term $1$, so the divisions are defined). Then

$$T^*_j(x; q) = \frac{q^j x}{K_j}.$$

For example, $T^*_1 = qx$ and $T^*_2 = q^2 x / (1 - q^2 x - q^3 x^2)$.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Lemma 10 (`integers-2025-A5-lem-10`).
