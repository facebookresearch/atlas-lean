# Dominance frontiers by walking up the dominator tree

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable, and its immediate dominators $\mathrm{idom}$. Call a node with at least two predecessors a *join point*. For each join point $b$ and each predecessor $p$ of $b$, walk up the dominator tree from $p$, adding $b$ to the [dominance frontier](dominance-frontiers.md) of each node visited, and stop on reaching $\mathrm{idom}(b)$, which is not visited.

**Theorem.** After all walks, the set collected for each node $X$ is $\mathrm{DF}(X)$. A node is visited in a walk for $b$ only if $b \in \mathrm{DF}$ of that node, so, with duplicate insertions suppressed, the walks take time proportional to the number of edges plus $\sum_X |\mathrm{DF}(X)|$.

**Proof idea.** A node $Y$ with one predecessor $P$ is in the dominance frontier of no node: every path to $Y$ passes through $P$, so a node that dominates $P$ dominates $Y$, and it is not $Y$ itself, since a path from the entry to $P$ avoiding $Y$ exists. For a join point $b$, the nodes that dominate a predecessor $p$ but not strictly $b$ are exactly the ancestors of $p$ in the dominator tree, $p$ included, below $\mathrm{idom}(b)$.

## Depends on

- [Dominance frontiers](dominance-frontiers.md)

## Sources

- K. D. Cooper, T. J. Harvey and K. Kennedy, *A Simple, Fast Dominance Algorithm*, Rice University Computer Science Technical Report TR-06-33870: section "Dominance Frontiers" (the observations on join points and the walks up the dominator tree, Figure 5) and its "Complexity Analysis" (the number of nodes touched equals the sum of the sizes of the dominance-frontier sets).
