# Johnson-Lindenstrauss lemma for n-point subsets of Euclidean space

There is an absolute constant $C$ such that for all $n \ge 2$, $d \ge 1$ and $0 < \varepsilon < 1$,

$$
m(n, d, \varepsilon) \le \min\{d, \; n, \; \lceil C\varepsilon^{-2}\log n\rceil\}.
$$

Moreover, the projection onto a uniformly random $k$-dimensional subspace scaled by $\sqrt{d/k}$ with $k = \lceil C\varepsilon^{-2}\log n\rceil$ satisfies the two-sided bound for all pairs of a fixed $n$-point set simultaneously with probability at least $1 - 1/n$, so such an embedding is found by a randomized algorithm in polynomial time.

## Proof sketch

The bounds $d$ and $n$ come from the identity and from projecting onto the span of $X$ (dimension at most $n - 1$). For the third bound, apply the distributional Johnson–Lindenstrauss lemma to each of the $\binom{n}{2}$ difference vectors $x - y$ with failure probability $\delta = n^{-3}$; by linearity the map preserves $\|x - y\|_2^2$ up to $1 \pm \varepsilon$ for each pair, and the union bound over pairs leaves failure probability at most $1/n$.

## Depends on

- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)
- [Distributional Johnson–Lindenstrauss lemma](../probabilistic-analysis-tools/distributional-johnsonlindenstrauss-lemma.md)

## Proof depends on

- [Distributional Johnson–Lindenstrauss lemma](../probabilistic-analysis-tools/distributional-johnsonlindenstrauss-lemma.md)

## Sources

- William B. Johnson, Joram Lindenstrauss, "Extensions of Lipschitz mappings into a Hilbert space", Contemp. Math. 26 (1984).
