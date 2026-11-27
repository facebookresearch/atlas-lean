# Pătraşcu–Viola lower bound for succinct rank

In the cell-probe model with cells of $w \ge \log_2 n$ bits, every data structure that answers $\mathrm{Rank}$ queries, or $\mathrm{Select}$ queries, on an array of $n$ bits by probing at most $t$ cells uses at least $n + n / w^{O(t)}$ bits of space (Theorem 1.1). For $w = \Theta(\log n)$ this bound matches Pătraşcu's succincter upper bound $n + n/((\log n)/t)^t$ up to the difference between $(\log n)^t$ and $((\log n)/t)^t$, which is immaterial for $t \le (\log n)^{1-\varepsilon}$. For an array of $n$ bits containing exactly $m$ ones, the same model with $w \ge \log_2 n$ requires at least $\log_2 \binom{n}{m} + m/w^{O(t)}$ bits (Theorem 1.2).

## Proof sketch

Take the input uniformly at random and augment the cell-probe model with a small number of *published bits* that queries read for free. The main lemma shows that, while fewer than about $n$ bits are published and the redundancy is small, there is a small set of cells that a constant fraction of queries probe; publishing those cells lowers the probe complexity of these queries by one. Iterating $t$ times drives the probe complexity to zero with fewer than $n$ published bits, which cannot determine a random $n$-bit array, unless the redundancy is at least $n / w^{O(t)}$.

## Depends on

- [Succinct rank with a probe budget](succinct-rank-tradeoff-problem.md)
- [The cell-probe model](../advanced-data-structures/the-cell-probe-model.md)
- [Pătraşcu's succincter rank and select](succincter-rank-upper-bound.md)

## Sources

- Mihai Pătraşcu, Emanuele Viola, "Cell-Probe Lower Bounds for Succinct Partial Sums", SODA (2010).
- Huacheng Yu, "Optimal Succinct Rank Data Structure via Approximate Nonnegative Tensor Decomposition", STOC (2019), arXiv:1811.02078.
