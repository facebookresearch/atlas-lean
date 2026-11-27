# Converging paths meet in an iterated dominance frontier

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable. If $X \ne Y$ and nonnull paths from $X$ to $Z$ and from $Y$ to $Z$ [converge](converging-paths-and-join-sets.md) at $Z$, then

$$Z \in \mathrm{DF}^+(\{X\}) \cup \mathrm{DF}^+(\{Y\}),$$

where $\mathrm{DF}^+$ is the [iterated dominance frontier](dominance-frontiers.md). Consequently, for every set $S$ of nodes, $J(S) \subseteq \mathrm{DF}^+(S)$.

**Proof idea.** Let $X'$ and $Y'$ be the nodes given by [the path lemma](paths-meet-the-iterated-dominance-frontier.md) for the two paths. If $X'$ lies on the path from $Y$, then convergence forces $X' = Z$. Either the path lemma already places $Z$ in $\mathrm{DF}^+(\{X\})$, or $Z = X$ and $X$ dominates every node of the path from $X$; then $X$ dominates the predecessor of $Z$ on that path but does not strictly dominate $Z$, so $Z \in \mathrm{DF}(X)$; symmetrically if $Y'$ lies on the path from $X$. Otherwise $X'$ strictly dominates every node of the path from $Y$, in particular $Y'$, and symmetrically $Y'$ strictly dominates $X'$, which is impossible.

## Depends on

- [Converging paths and join sets](converging-paths-and-join-sets.md)
- [Dominance frontiers](dominance-frontiers.md)

## Proof depends on

- [Paths meet the iterated dominance frontier](paths-meet-the-iterated-dominance-frontier.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 4.3: Lemma 5 with its proof, and Lemma 6.
