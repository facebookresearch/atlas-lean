# Paths meet the iterated dominance frontier

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable, and let $\mathrm{DF}^+$ be the [iterated dominance frontier](dominance-frontiers.md). For every nonnull path $p$ from $X$ to $Z$ in $G$, some node $X'$ of $\{X\} \cup \mathrm{DF}^+(\{X\})$ on $p$ dominates $Z$. Moreover, unless $X$ dominates every node on $p$, the node $X'$ can be chosen in $\mathrm{DF}^+(\{X\})$.

**Proof.** If $X$ dominates every node on $p$, take $X' = X$. Otherwise let $p$ be $X = X_0, \dots, X_J = Z$. The first node not dominated by $X$ has a predecessor on $p$ dominated by $X$, so it lies in $\mathrm{DF}(X)$. Let $X' = X_j$ for the largest $j$ with $X_j \in \mathrm{DF}^+(\{X\})$. If $X'$ did not dominate $Z$, the first $X_k$ with $k > j$ not dominated by $X'$ would lie in $\mathrm{DF}(X') \subseteq \mathrm{DF}^+(\{X\})$, contradicting the choice of $j$.

## Depends on

- [Dominance frontiers](dominance-frontiers.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 4.3: Lemma 4 with its proof.
