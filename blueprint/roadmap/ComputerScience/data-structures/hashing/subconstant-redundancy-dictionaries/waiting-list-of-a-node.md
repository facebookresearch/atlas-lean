# Waiting list of a dictionary-tree node

In the multi-level dictionary tree, each node $u$ at level $\ell$ keeps a *waiting list* of bounded capacity $2\delta_\ell$ holding pairs (identifier at level $\ell$, identifier at level $\ell - 1$) of keys that have been routed to $u$ but are not yet stored in its children, for instance while a child subtree is being rebuilt. Queries check the waiting list before descending, so the represented dictionary includes its keys; its size is charged to the redundancy budget.

## Depends on

- [Multi-level dictionary tree with subconstant wasted bits](multi-level-dictionary-tree.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
