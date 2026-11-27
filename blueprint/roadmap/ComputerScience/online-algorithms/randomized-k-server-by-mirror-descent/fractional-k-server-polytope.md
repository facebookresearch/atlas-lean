# Fractional k-server on a tree

Let $T$ be an HST with leaf set $L$ and, for a node $u$, let $L_u$ be the leaves below $u$ and $w_u$ the length of the edge from $u$ to its parent. A *fractional $k$-server state* is a leaf measure $z \in \mathbb{R}_{\ge 0}^{L}$ of mass $\sum_{\ell \in L} z_\ell = k$; a single leaf may carry mass larger than $1$. For each node $u$ write $z_u = \sum_{\ell \in L_u} z_\ell$. Moving from $z$ to a state $z'$ of the same mass costs the transportation distance between them, which equals $\sum_{u \ne r} w_u |z_u - z'_u|$ for the root $r$. A *fractional $k$-server algorithm* is an online sequence $z^{(0)}, z^{(1)}, \dots$ of fractional $k$-server states with $z^{(0)}$ integral and $z^{(t)}_{\ell_t} \ge 1$ for the leaf $\ell_t$ requested at time $t \ge 1$; its cost is the total movement $\sum_{t \ge 0} \sum_{u \ne r} w_u |z^{(t)}_u - z^{(t+1)}_u|$.

## Depends on

- [Hierarchically separated trees](../metrical-task-systems-and-hst-embeddings/hierarchically-separated-tree.md)
- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)

## Sources

- Sébastien Bubeck, Michael B. Cohen, Yin Tat Lee, James R. Lee, Aleksander Mądry, "k-Server via Multiscale Entropic Regularization", STOC (2018), arXiv:1711.01085, Section 3 and Lemma 3.1.
