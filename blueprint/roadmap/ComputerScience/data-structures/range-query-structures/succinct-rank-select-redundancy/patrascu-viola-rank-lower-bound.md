# Pătraşcu–Viola lower bound for succinct rank

The bounds below are asymptotic in $n$ and are stated for the nondegenerate regimes; the endpoints are handled separately at the end. In the cell-probe model with cells of $w \ge \log_2 n$ bits, in the regime where the redundancy term $n/w^{O(t)}$ is at least $1$ (in particular $t \le \log_2 n$, beyond which the source notes there is nothing to prove, and $w^{O(t)} \le n$), every data structure that answers $\mathrm{Rank}$ queries, or $\mathrm{Select}$ queries, on an array of $n$ bits by probing at most $t$ cells uses at least $n + n / w^{O(t)}$ bits of space (Theorem 1.1). For $w = \Theta(\log n)$ this bound matches Pătraşcu's succincter upper bound $n + n/((\log n)/t)^t$ up to the difference between $(\log n)^t$ and $((\log n)/t)^t$, which is immaterial for $t \le (\log n)^{1-\varepsilon}$. For an array of $n$ bits containing exactly $m$ ones, in the regime $1 \le m \le n/2$, where the ones are not dense (the setting in which the source introduces the problem), and where $m/w^{O(t)} \ge 1$, the same model with $w \ge \log_2 n$ requires at least $\log_2 \binom{n}{m} + m/w^{O(t)}$ bits (Theorem 1.2). The endpoints fall outside these statements: if $w \ge n$, a single cell stores an arbitrary $n$-bit input exactly and one probe answers every query with $n$ bits of space; if $m = n$ (or $m = 0$) the array is determined, $\mathrm{Rank}(i)$ and $\mathrm{Select}(j)$ need no stored bits and $\log_2\binom{n}{m} = 0$; and for $m$ close to $n$ a structure storing the few zeros is far more compact, for example $m = n - 1$ with one cell holding the position of the zero.

## Proof sketch

Take the input uniformly at random and augment the cell-probe model with a small number of *published bits* that queries read for free. The main lemma shows that, while fewer than about $n$ bits are published and the redundancy is small, there is a small set of cells that a constant fraction of queries probe; publishing those cells lowers the probe complexity of these queries by one. Iterating $t$ times drives the probe complexity to zero with fewer than $n$ published bits, which cannot determine a random $n$-bit array, unless the redundancy is at least $n / w^{O(t)}$.

## Depends on

- [Succinct rank with a probe budget](succinct-rank-tradeoff-problem.md)
- [The cell-probe model](../advanced-data-structures/the-cell-probe-model.md)
- [Pătraşcu's succincter rank and select](succincter-rank-upper-bound.md)

## Sources

- Mihai Pătraşcu, Emanuele Viola, "Cell-Probe Lower Bounds for Succinct Partial Sums", SODA (2010), Theorems 1.1 and 1.2 and Section 2.
- Huacheng Yu, "Optimal Succinct Rank Data Structure via Approximate Nonnegative Tensor Decomposition", STOC (2019), arXiv:1811.02078.
