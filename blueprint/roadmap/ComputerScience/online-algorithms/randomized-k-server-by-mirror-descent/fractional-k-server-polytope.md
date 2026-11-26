# Fractional k-server on a tree

Let $T$ be an HST with leaf set $L$ and, for a node $u$, let $L_u$ be the leaves below $u$ and $w_u$ the length of the edge from $u$ to its parent. A *fractional $k$-server state* is a vector $z \in [0, 1]^{L}$ with $\sum_{\ell \in L} z_\ell = k$, the *anti-server* mass $1 - z_\ell$ at each leaf; for each node $u$ write $z_u = \sum_{\ell \in L_u} z_\ell$. Moving from $z$ to $z'$ costs $\sum_u w_u |z_u - z'_u|$, and a request at leaf $\ell$ requires $z_\ell = 1$ (equivalently zero anti-server mass at $\ell$).

## Depends on

- [Hierarchically separated trees](../metrical-task-systems-and-hst-embeddings/hierarchically-separated-tree.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085.
