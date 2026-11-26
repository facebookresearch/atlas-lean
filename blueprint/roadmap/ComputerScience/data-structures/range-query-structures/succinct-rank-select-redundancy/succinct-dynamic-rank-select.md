# Succinct dynamic rank/select with sub-linear redundancy

For $U = n^{O(1)}$, there is a dynamic rank/select dictionary on a set $S \subseteq [U]$ of at most $n$ elements that supports insert, delete, rank and select in amortized expected time $O(1 + \log n / \log \log U)$ and uses $\log_2 \binom{U}{n} + n / 2^{(\log n)^{\Omega(1)}} + (\log U)^{O(1)}$ bits. This answers the question of Pibiri and Venturini and is the first dynamic structure to bypass the tree-structure bottleneck.

## Proof sketch

Partition the key space into blocks of $(\log n)^{\Theta(1)}$ elements, each stored as a compressed tabulation-weighted treap whose redundancy is $O(\log U)$ bits, so the total block redundancy is $n / (\log n)^{\Omega(1)}$ times smaller than the number of blocks would otherwise force; a higher-level structure locates blocks and maintains their counts with fusion-style word parallelism in $O(\log n/\log\log U)$ time. Recursing the same idea on the top-level structure drives the redundancy down to $n / 2^{(\log n)^{\Omega(1)}}$.

## Depends on

- [Dynamic ordered dictionary with rank and select](dynamic-ordered-dictionary-with-rank.md)
- [The tree-structure bottleneck for succinct dynamic dictionaries](tree-structure-bottleneck.md)

## Proof depends on

- [The compressed tabulation-weighted treap](compressed-tabulation-weighted-treap.md)

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
