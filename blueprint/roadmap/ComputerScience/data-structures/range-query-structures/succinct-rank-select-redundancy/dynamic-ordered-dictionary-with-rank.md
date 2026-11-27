# Dynamic ordered dictionary with rank and select

A *dynamic rank/select dictionary* (dynamic fully indexable dictionary) maintains a set $S \subseteq [U] = \{0, \dots, U-1\}$ under $\mathrm{insert}(x)$ for $x \in [U] \setminus S$, $\mathrm{delete}(x)$ for $x \in S$, $\mathrm{rank}(x) = |\{y \in S : y < x\}|$ and $\mathrm{select}(i)$, which returns the $i$-th smallest element of $S$ if it exists. With $n = |S|$ the current size, any such structure needs at least $\lceil \log_2 \binom{U}{n} \rceil$ bits, and a structure using $\log_2 \binom{U}{n} + R$ bits has *redundancy* $R$.

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
- Paul F. Dietz, "Optimal Algorithms for List Indexing and Subset Rank", WADS (1989).
