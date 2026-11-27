# Routing by child-minimum ranks

At an internal node of a multiway predecessor tree with cached child minima $m_1 < \dots < m_d$, the inclusive rank $\rho$ of a query $q$ among $m_1, \dots, m_d$ determines the search: if $\rho = 0$ every key below the node exceeds $q$ and the search stops, and otherwise the predecessor of $q$ lies in child $\rho$. Thus a constant-time node rank replaces the linear scan over children, and a predecessor query costs one node rank per level.

## Proof sketch

The children's key ranges are consecutive and child $i$'s minimum is $m_i$; $q$'s predecessor lies in the last child whose minimum is at most $q$, which is child $\rho$.

## Depends on

- [Static multiway predecessor tree with cached minima](multiway-predecessor-tree.md)

## Sources

- M. L. Fredman and D. E. Willard, "Surpassing the Information Theoretic Bound with Fusion Trees", Journal of Computer and System Sciences 47(3), 1993.
