# Optimal tiling by dynamic programming

Fix a finite tile set and the additive cost model of [tilings of intermediate-code trees](tilings-of-intermediate-code-trees.md), in which the cost of a tiling is the sum of the costs of its tiles. For a tree $T$ and a node $u$ of $T$, let $c(u)$ be the least cost of a tiling of the subtree rooted at $u$, or $\infty$ if none exists. Then

$$c(u) = \min_{\tau \text{ matches at } u} \Bigl(\mathrm{cost}(\tau) + \sum_{w \in \mathrm{holes}_u(\tau)} c(w)\Bigr),$$

where $\mathrm{holes}_u(\tau)$ is the set of nodes matched by the holes of $\tau$ placed at $u$, and the minimum over no tiles is $\infty$. So an optimal tiling of a node is built from optimal tilings of the subtrees left uncovered by its root tile.

**Algorithm.** Compute $c(u)$ bottom up by this recurrence, remembering at each node its least cost and, when it is finite, a tile achieving it. If $c(\mathrm{root}) = \infty$, $T$ has no tiling, as with a tile set containing only a constant tile and a tree whose root is a temporary; otherwise the remembered tiles, read from the root, form a tiling of $T$ of least total cost. Each node is evaluated once, so a simple matcher that tests every tile at every node performs at most $|T| \cdot |\mathrm{tiles}|$ tests, and the algorithm runs in time polynomial in the size of $T$ for a fixed tile set.

**Proof.** The recurrence holds because the cost of a tiling is the cost of its root tile plus the costs of the tilings of the uncovered subtrees, which can be chosen independently. Induction on the height of $u$ shows that, when $c(u)$ is finite, the remembered tiles form a tiling of cost $c(u)$.

## Depends on

- [Tilings of intermediate-code trees](tilings-of-intermediate-code-trees.md)

## Sources

- A. C. Myers, *Instruction Selection*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/tiles/index.html>: section "Optimal tiling" (the additive cost approximation, optimal substructure, the memoized algorithm that tries all matching tiles and remembers the best tiling at each node, and the bound on the number of tile matches) and section "Summary".
