# Dynamic ordered dictionary with rank and select

A *dynamic rank/select dictionary* maintains a set $S \subseteq [U] = \{0, \dots, U-1\}$ with $|S| \le n$ under $\mathrm{insert}(x)$, $\mathrm{delete}(x)$, $\mathrm{rank}(x) = |\{y \in S : y < x\}|$ and $\mathrm{select}(i)$, which returns the $i$-th smallest element of $S$. Its space is compared with $\log_2 \binom{U}{|S|}$.

## Depends on

- [Succinct rank with a probe budget](succinct-rank-tradeoff-problem.md)

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
- Paul F. Dietz, "Optimal Algorithms for List Indexing and Subset Rank", WADS (1989).
