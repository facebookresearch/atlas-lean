# Pătraşcu–Viola lower bound for succinct rank

If a data structure answers $\mathrm{Rank}(k)$ queries on an $n$-bit array by probing $t$ cells of $w$ bits, then its space is at least $n + n / w^{O(t)}$ bits. The same tradeoff holds for $\mathrm{Select}$ and extends to sparse arrays. Together with the succincter upper bound, the redundancy/probe tradeoff for rank is $r = n / w^{\Theta(t)}$ for $w = \Theta(\log n)$.

## Proof sketch

Choose the input uniformly at random; a structure with tiny redundancy must store almost all of its bits as an almost-uniform string, so the cells probed by a query carry almost no information about bits outside them. Pătraşcu and Viola show, by a round-elimination style argument on the query's probe tree, that answering $\mathrm{Rank}$ at a random position then requires knowledge of too many independent block sums unless the redundancy is at least $n / w^{O(t)}$.

## Depends on

- [Succinct rank with a probe budget](succinct-rank-tradeoff-problem.md)

## Proof depends on

- [Succinct rank with a probe budget](succinct-rank-tradeoff-problem.md)

## Sources

- Mihai Pătraşcu, Emanuele Viola, "Cell-Probe Lower Bounds for Succinct Partial Sums", SODA (2010).
- Huacheng Yu, "Optimal Succinct Rank Data Structure via Approximate Nonnegative Tensor Decomposition", STOC (2019), arXiv:1811.02078.
