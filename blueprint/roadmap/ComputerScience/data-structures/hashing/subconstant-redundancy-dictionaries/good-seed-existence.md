# Existence of good seed assignments for the dictionary tree

In the polynomial-universe regime, for every key set of size at most $n$ the probability, over independently drawn node seeds, that some node of the multi-level dictionary tree overflows or underflows (receives more than $\overline{n}_\ell$ or fewer than $\underline{n}_\ell$ keys) or produces an identifier collision is less than $1$; in particular a good seed assignment exists, and the tree can be built bottom-up from any such assignment.

## Proof sketch

Each node's load is a sum of indicators that are highly independent under double tabulation, so a moment bound gives an exponentially small overflow probability in the node's expected load; a union bound over all nodes of the tree is below $1$ by the choice of the parameter schedule.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Proof depends on

- [Thorup's high independence of double tabulation](../word-ram-hash-families/high-independence-of-double-tabulation.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
