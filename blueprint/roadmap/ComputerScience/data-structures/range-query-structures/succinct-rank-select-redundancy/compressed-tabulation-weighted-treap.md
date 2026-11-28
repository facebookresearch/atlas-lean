# The compressed tabulation-weighted treap

Fix upper bounds $n_{\max}$ on the number of keys and $U_{\max}$ on the universe size, and word size $w = \Theta(\log U_{\max})$. The *compressed tabulation-weighted treap* is a dynamic balanced binary search tree storing a set of $n \le n_{\max}$ keys from a universe $[U]$, $U \le U_{\max}$, that supports insertions and deletions in $O(\log^3 n)$ expected time and rank and select queries in $O(\log^2 n)$ expected time on the word RAM. It uses $\log_2 \binom{U}{n} + O(w)$ bits of space, a redundancy of $O(\log U_{\max})$ bits, given access to a static lookup table of $\mathrm{poly}(n_{\max}, \log U_{\max})$ words that depends only on $n_{\max}$, $U_{\max}$ and shared randomness and can be shared by all instances; during an operation it may temporarily use $O(nw)$ bits. If $n$, $n_{\max}$, $U$ and $U_{\max}$ are given for free, the redundancy drops to $O(1)$ bits.

## Proof sketch

A treap is strongly history independent: given its random weight function, the tree shape is determined by the key set alone, so in principle the same bits can encode both the keys and the tree. The tabulation-weighted treap redesigns the weight function so that the boundary between keys and tree structure blurs, and the tree is then encoded as a recursive tree of random variables (the rank of each subtree's pivot and its weight, given the subtree's size and key range). Each variable is entropy-coded against its exact distribution with lookup-table-driven encoders, which yields an explicit encoding whose length exceeds $\log_2 \binom{U}{n}$ by only $O(w)$ bits and which can still be navigated and updated in polylogarithmic time.

## Depends on

- [Information-theoretic space bound and redundancy of a dictionary](../../hashing/stable-and-tiny-pointer-hash-tables/information-theoretic-space-and-redundancy.md)
- [Dynamic ordered dictionary with rank and select](dynamic-ordered-dictionary-with-rank.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
