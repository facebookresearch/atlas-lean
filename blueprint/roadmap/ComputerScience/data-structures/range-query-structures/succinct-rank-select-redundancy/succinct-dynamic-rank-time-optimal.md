# Time optimality of succinct dynamic rank/select

For $n \le U/2$, $U = n^{O(1)}$ and $w = \Theta(\log U)$, the $O(1 + \log n/\log\log U) = O(\log n / \log \log n)$ operation time of the succinct dynamic rank/select dictionary with sub-linear redundancy is optimal, regardless of space, among cell-probe structures whose updates take $(\log n)^{O(1)}$ amortized probes. The condition $n \le U/2$ is needed: at $n = U$ every key is present and rank is trivial.

## Proof sketch

For $n \le U/2$, the Fredman–Saks bound $t_q = \Omega(\log n / \log(t_u w))$ applies, and it equals $\Omega(\log n/\log\log n)$ when $t_u w = (\log n)^{O(1)}$; moreover $\log\log U = \Theta(\log\log n)$ for polynomial universes.

## Depends on

- [Succinct dynamic rank/select with sub-linear redundancy](succinct-dynamic-rank-select.md)
- [Dynamic ordered dictionary with rank and select](dynamic-ordered-dictionary-with-rank.md)
- [The cell-probe model](../advanced-data-structures/the-cell-probe-model.md)

## Proof depends on

- [Fredman–Saks lower bound for dynamic rank](dynamic-rank-time-lower-bound.md)

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
- Michael L. Fredman, Michael E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", STOC (1989).
