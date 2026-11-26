# Padding entropy and seed sizes in the dictionary tree

In the multi-level dictionary tree with effective redundancy parameter $R'$, padding the universe with sentinels to the size required by the schedule increases $\log_2 \binom{U}{n} + n \log_2 V$ by at most $2R' + 1$ bits; at every non-leaf level $\ell$ the squared bit length of the child-router seed is at most the level's minimum node capacity, so seeds use a vanishing fraction of a node's space; and the identifier-compressor seeds, waiting lists, leaf deficits, inner tables and root directory each contribute $O(R')$ bits in total.

## Proof sketch

Sentinels are a lower-order fraction of the keys, chosen so that their entropy contribution is at most $2R'+1$ bits. The seed and waiting-list bounds follow from the parameter schedule, in which node capacities shrink slowly enough that per-node overheads sum to $O(R')$ over all levels.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)
- [Waiting list of a dictionary-tree node](waiting-list-of-a-node.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
