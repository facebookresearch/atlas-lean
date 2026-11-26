# Space of the multi-level dictionary tree is OPT + O(R)

There is a universal constant $C$ such that, for every admissible parameter regime (polynomial universe $n^{1+\alpha_{\min}} \le U \le n^{1+\alpha_{\max}}$, any value bound $V \ge 1$, and redundancy parameter $R$ in the allowed range below $n$), the total number of bits of the canonical multi-level dictionary tree — leaf minimaps, inner storage tables, metadata, waiting lists and all hash seeds — is at most

$$
\log_2 \binom{U}{n} + n \log_2 V + C \cdot R .
$$

In particular, with $R = o(n)$ the dictionary wastes $o(1)$ bits per key.

## Proof sketch

Information is conserved down the tree: the bits of a node's children, together with the routing information implicit in which child stores a key, add up to the node's share of $\log_2\binom{U}{n} + n\log_2 V$, up to slack terms. Each leaf wastes at most two bits, and the slack of inner nodes, waiting lists and seeds is bounded by the parameter schedule so that the sum over the whole tree is $O(R)$.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)
- [Information-theoretic space bound for dictionaries](../dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [A full minimap wastes at most two bits](full-minimap-wastes-two-bits.md)
- [Existence of good seed assignments for the dictionary tree](good-seed-existence.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
