# Postdominating a successor

Let $G$ be a control-flow graph with an exit node reachable from every node, with the postdominance relation used in [control dependence](control-dependence.md). For nodes $X$ and $Y$, $Y$ postdominates a successor of $X$ if and only if there is a nonnull path $p$ from $X$ to $Y$ such that $Y$ postdominates every node after $X$ on $p$.

**Proof.** Suppose $Y$ postdominates a successor $U$ of $X$. Take any path from $U$ to the exit and its initial segment $r$ up to the first occurrence of $Y$. Each node $V$ on $r$ is postdominated by $Y$: otherwise a path from $U$ along $r$ to $V$ and then to the exit would avoid $Y$. The edge $X \to U$ followed by $r$ is the required path. Conversely, the first node after $X$ on such a path is a successor of $X$ postdominated by $Y$.

## Depends on

- [Control dependence](control-dependence.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 6: the definition of postdominance and Lemma 11 with its proof.
