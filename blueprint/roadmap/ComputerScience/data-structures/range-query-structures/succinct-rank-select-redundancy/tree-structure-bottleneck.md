# The tree-structure bottleneck for succinct dynamic dictionaries

The *tree-structure bottleneck* is the obstacle, named by Kuszmaul, Liang and Zhou, that every known time-optimal dynamic rank/select dictionary stores a large portion of its keys (at least $\tilde{\Omega}(n)$ of them) in some dynamic tree structure, and encoding the changing shape of that tree in a navigable way already appears to cost $\tilde{\Omega}(n)$ bits of redundancy, so that without new techniques one could hope at best for redundancy $n / (\log n)^{O(1)}$. Before their work the best time-optimal dynamic solution, due to Pibiri and Venturini, had redundancy $O(n)$, and whether redundancy significantly below $O(n)$ is achievable was their open question. The bottleneck is an informal barrier, not a theorem.

## Depends on

- [Dynamic ordered dictionary with rank and select](dynamic-ordered-dictionary-with-rank.md)

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
