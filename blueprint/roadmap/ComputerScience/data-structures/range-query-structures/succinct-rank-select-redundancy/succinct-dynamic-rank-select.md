# Succinct dynamic rank/select with sub-linear redundancy

On the word RAM with $w = \Theta(\log U)$-bit words, there is a dynamic rank/select dictionary on a set $S \subseteq [U]$ of current size $n$ whose insertions and deletions take amortized expected time $O(1 + \log n / \log w)$, whose rank and select queries take expected time $O(1 + \log n / \log w)$, and which uses $\log_2 \binom{U}{n} + O\big(wn / 2^{(\log n/\log w)^{1/3}}\big) + (\log U)^{O(1)}$ bits at all times. For $U = n^{O(1)}$ the time is $O(1 + \log n/\log\log U)$ and the space is $\log_2 \binom{U}{n} + n / 2^{(\log n)^{\Omega(1)}} + (\log U)^{O(1)}$ bits. This answers the question of Pibiri and Venturini whether redundancy $o(n)$ is possible, and is the first dynamic structure to bypass the tree-structure bottleneck.

## Proof sketch

Partition the universe into intervals (blocks) holding between $B$ and $4B$ keys, with $B = 2^{\Theta((\log n/\log w)^{1/3})}$, and store each block as a compressed tabulation-weighted treap, which costs $O(w)$ bits of redundancy per block and $O(\log^3 B) = O(\log n / \log w)$ expected time per operation. The total block redundancy is then $O(wn/B)$, and a time-optimal top-level structure over the $O(n/B)$ blocks, whose own $O(1)$ redundancy per entry is affordable, locates the block of a key or rank; rebuilding with a new $B$ handles large changes of $n$.

## Depends on

- [Dynamic ordered dictionary with rank and select](dynamic-ordered-dictionary-with-rank.md)
- [The tree-structure bottleneck for succinct dynamic dictionaries](tree-structure-bottleneck.md)

## Proof depends on

- [The compressed tabulation-weighted treap](compressed-tabulation-weighted-treap.md)

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
