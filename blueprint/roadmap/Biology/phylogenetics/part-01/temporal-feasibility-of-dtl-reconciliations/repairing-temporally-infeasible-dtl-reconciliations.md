# Repairing temporally infeasible DTL reconciliations

**Setting.** Let $G$ (gene tree) and $S$ (species tree) be rooted binary trees with a leaf map from $G$ to $S$. A *DTL-scenario* maps every node $g$ of $G$ to a node $\mathcal M(g)$ of $S$ and labels internal nodes as speciations, duplications or transfers (a transfer also names a takeoff and landing location), subject to the usual consistency constraints; its cost is $C_\Delta|\Delta| + C_\Theta|\Theta| + C_\Lambda\cdot\mathrm{Loss}$ for the duplications $\Delta$, transfers $\Theta$ and losses. On an undated species tree, maximum parsimony reconciliations (MPRs) are computable in $O(|G||S|)$ time, but they may be *temporally infeasible*: no dating of $S$ makes every transfer join contemporaneous lineages; finding a temporally feasible MPR is NP-complete. The *temporal feasibility graph* $F$ has the internal nodes of $S$ and $G$ as vertices and arcs for ancestor-before-descendant constraints in each tree, for each gene node relative to its associated species nodes, and for the contemporaneity of each transfer's takeoff and landing sites.

**Criterion.** A DTL-scenario admits a temporally consistent dating if and only if $F$ is acyclic; a topological order of $F$ then gives a feasible dating of $S$.

**Repair algorithm.** Starting from an MPR, repeatedly pick a gene node $g$ on a cycle of $F$ such that no other gene node on a cycle is mapped below $\mathcal M(g)$, and pull it up in $S$: to the parent of $\mathcal M(g)$ if $g$ is a duplication or transfer, or to the edge above $\mathcal M(g)$ if it is a speciation; recompute $F$; stop when $F$ is acyclic.

**Theorem.** Let $h_G, h_S$ be the heights of $G$ and $S$ and $k$ the number of transfers in the initial MPR.

1. The algorithm terminates and returns a valid, temporally consistent DTL-scenario.
2. Its worst-case running time is $O(|G|^3 h_S + |G|^2|S|h_S)$.
3. Only transfer nodes and their ancestors are ever moved, and the repair introduces at most $k h_G$ new duplications and at most $k h_G h_S$ new losses, bounding the cost increase over the (possibly infeasible) optimum.

## Depends on

- [Topological order](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/topological-sorting/is-topological-order.md)

## Expansion

Every cycle of $F$ must use a contemporaneity arc of some transfer, because the tree-order arcs alone are acyclic; hence the node chosen for repair lies above some transfer (it is an ancestor of a transfer node). Pulling a lowest such node up removes the offending order constraint while keeping the scenario valid, and a node can move at most $h_S$ times, which bounds the number of iterations by $|I(G)| h_S$; each iteration costs $O(|G|^2 + |G||S|)$ for cycle detection. The cost bound follows by charging new duplications to ancestors of transfers (fewer than $h_G$ per transfer) and new losses to the at most $h_S$ steps each such node can move.

## Sources

- W. Ma, D. Smirnov and R. Libeskind-Hadas, "DTL reconciliation repair", *BMC Bioinformatics* (2017), Definitions 1–3, construction of the temporal feasibility graph, Algorithms 1–3, Lemmas 1–5 and Theorems 1–3. <https://doi.org/10.1186/s12859-017-1463-9> (PMC5374596)
