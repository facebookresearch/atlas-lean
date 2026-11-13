# Sum of an eventually periodic sequence

Let $K$ be a field of characteristic zero, let
$f : \mathbb{N} \to K$, and let $L \ge 1$ and $D \ge 1$ be natural numbers such that
$f(i + L) = f(i)$ for all $i \ge D$. Let $\bar f = \frac{1}{L} \sum_{k=D}^{D+L-1} f(k)$ be the
average over one period. Then for every natural number $N \ge D - 1$,

$$\sum_{i=1}^{N} f(i) = \sum_{i=1}^{D-1} f(i) + (N - D + 1) \bar f +
\sum_{k=1}^{(N-D+1) \bmod L} \left(f(k + D - 1) - \bar f\right).$$

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Corollary 1 (Sum of an eventually periodic sequence).
