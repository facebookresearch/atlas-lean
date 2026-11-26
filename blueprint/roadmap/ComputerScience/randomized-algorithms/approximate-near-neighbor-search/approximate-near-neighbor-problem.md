# Approximate near-neighbour problem

Let $(X, \mathrm{dist})$ be a metric space, $r > 0$ and $c > 1$. The *$(c, r)$-approximate near-neighbour problem* asks for a data structure over a finite point set $P \subseteq X$ that, given a query $q$ such that some point of $P$ lies within distance $r$ of $q$, returns some point of $P$ within distance $c r$ of $q$. A randomized structure *fails* on $q$ if it returns nothing although a point within distance $r$ exists.

## Sources

- P. Indyk and R. Motwani, "Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality", Proceedings of the 30th ACM Symposium on Theory of Computing (STOC), 1998.
- S. Har-Peled, P. Indyk and R. Motwani, "Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality", Theory of Computing 8(14), 2012.
