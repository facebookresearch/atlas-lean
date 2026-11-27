# Space of the multi-level dictionary tree is OPT + O(R)

There are constants $C$ and $n_0$, depending only on $\alpha_{\min}$ and $\alpha_{\max}$, such that for every $n \ge n_0$, every universe size $U$ with $n^{1+\alpha_{\min}} \le U \le n^{1+\alpha_{\max}}$, every value bound $V \ge 1$, word size $w = \Omega(\log(UV))$ and every redundancy parameter $R$ with $n / (\log_2 n)^{0.1} \le R \le n / 2^{\log^* n}$ (the regime $R \ge n / \log^{0.1} n$ of Theorem 1.1 of Li, Liang, Yu and Zhou, constructed in their Section 5), the total number of bits of the multi-level dictionary tree holding $n$ or $n - 1$ keys — leaf minimaps, inner storage tables, metadata, waiting lists and all hash seeds — is at most

$$
\log_2 \binom{U}{n} + n \log_2 V + C \cdot R .
$$

In particular, with $R = o(n)$ in this range the dictionary wastes $o(1)$ bits per key.

## Proof sketch

Information is conserved down the tree: the bits of a node's children, together with the routing information implicit in which child stores a key, add up to the node's share of $\log_2\binom{U}{n} + n\log_2 V$, up to slack terms. Each leaf wastes at most three bits, and the slack of storage tables, waiting lists, rounding and seeds sums to $O(R)$ over the whole tree.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [A full minimap wastes at most three bits](full-minimap-wastes-three-bits.md)
- [Existence of good seed assignments for the dictionary tree](good-seed-existence.md)
- [Padding entropy and seed sizes in the dictionary tree](padding-entropy-and-seed-sizes.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
