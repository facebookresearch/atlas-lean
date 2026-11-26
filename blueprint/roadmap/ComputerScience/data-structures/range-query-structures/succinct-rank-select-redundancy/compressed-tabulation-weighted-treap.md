# The compressed tabulation-weighted treap

There is a dynamic balanced binary search tree over $n$ keys from $[U]$, the *compressed tabulation-weighted treap*, supporting insertions, deletions and searches in $(\log n)^{O(1)}$ time, using a static lookup table of $\mathrm{poly}(n) + (\log U)^{O(1)}$ bits shared by all instances, whose total space redundancy beyond $\log_2 \binom{U}{n}$ is $O(\log U)$ bits; if $n$ and $U$ are given for free, the redundancy drops to $O(1)$ bits.

## Proof sketch

Treap priorities are derived from the keys by a tabulation-based weighting, so the tree shape is a deterministic function of the key set and need not be stored. The tree is then encoded top-down: at each node the split induced by the root key is encoded by arithmetic coding against the exact conditional distribution of the split, and the lookup table supplies the required cumulative counts. Since the code is matched to the distribution of the whole key set, the total length is within $O(\log U)$ bits of $\log_2 \binom{U}{n}$.

## Depends on

- [The tree-structure bottleneck for succinct dynamic dictionaries](tree-structure-bottleneck.md)
- [Information-theoretic space bound and redundancy of a dictionary](../../hashing/stable-and-tiny-pointer-hash-tables/information-theoretic-space-and-redundancy.md)

## Proof depends on

- [The tree-structure bottleneck for succinct dynamic dictionaries](tree-structure-bottleneck.md)
- [Information-theoretic space bound and redundancy of a dictionary](../../hashing/stable-and-tiny-pointer-hash-tables/information-theoretic-space-and-redundancy.md)

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
