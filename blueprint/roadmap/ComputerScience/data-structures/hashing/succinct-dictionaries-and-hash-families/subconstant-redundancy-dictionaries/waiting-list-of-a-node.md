# Waiting list of a dictionary-tree node

In the multi-level dictionary tree, each non-root node $u$ at level $\ell \ge 2$ keeps a *waiting list* of capacity $\overline{n}_\ell - \underline{n}_\ell \le 2\Delta_\ell$ holding pairs (identifier at level $\ell$, identifier at level $\ell - 1$) of keys that have been routed to $u$ but are stored at an ancestor of $u$, so that after a deletion from the subtree of $u$ a key stored at an ancestor can be found and pulled down to refill it. The list is auxiliary: its keys are stored at ancestors, and its at most $2\Delta_\ell (1 + I_\ell + I_{\ell-1})$ bits are charged to the redundancy budget.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
