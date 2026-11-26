# Iterated dominance frontiers are iterated joins

Let $G$ be a control-flow graph with an entry node that has no predecessors and from which every node is reachable. Nonnull paths $p : X_0 \to \dots \to X_J$ and $q : Y_0 \to \dots \to Y_K$ *converge* at a node $Z$ if $X_0 \ne Y_0$, $X_J = Z = Y_K$, and $X_j = Y_k$ implies $j = J$ or $k = K$. One of the paths may be a cycle through $Z$. For a set $S$ of nodes, the *join set* $J(S)$ is the set of nodes $Z$ at which two nonnull paths starting at two distinct nodes of $S$ converge. The *iterated join* $J^+(S)$ is the limit of $J_1 = J(S)$, $J_{i+1} = J(S \cup J_i)$. Let $\mathrm{DF}^+$ be the [iterated dominance frontier](dominance-frontiers.md).

1. For every set $S$ of nodes, $J(S) \subseteq \mathrm{DF}^+(S)$, and hence $J^+(S) \subseteq \mathrm{DF}^+(S)$.
2. If $S$ contains the entry node, then $\mathrm{DF}(S) \subseteq J(S)$, and hence $\mathrm{DF}^+(S) \subseteq J^+(S)$.
3. Consequently, treating the entry node as an assignment to every variable $V$, the set of nodes that need a $\varphi$-function for $V$ in [minimal SSA form](dominance-and-static-single-assignment-form.md), namely $J^+(S)$ for the set $S$ of nodes that assign to $V$, equals $\mathrm{DF}^+(S)$. A worklist over $\mathrm{DF}$ therefore places exactly the $\varphi$-functions of minimal SSA form.

Part 1 rests on a lemma: for every nonnull path from $X$ to $Z$, some node of $\{X\} \cup \mathrm{DF}^+(\{X\})$ on the path dominates $Z$. The hypothesis on the entry is needed: with an edge from a node $a$ back to the entry $r$, $r \in \mathrm{DF}(\{r\})$ while $J(\{r\}) = \emptyset$. Part 2 holds because, for $Y \in \mathrm{DF}(X)$, a path from $X$ to $Y$ through nodes dominated by $X$ and a path from the entry to $Y$ through nodes not dominated by $X$ converge at $Y$.

## Depends on

- [Dominance frontiers](dominance-frontiers.md)
- [Dominance and static single assignment form](dominance-and-static-single-assignment-form.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991:
    - Section 2: the definition of convergence of nonnull paths, conditions (1)–(3);
    - Section 3: the definition of translation to minimal SSA form and of the nodes that need $\varphi$-functions;
    - Section 4.3: join sets and iterated joins, Lemma 4, Lemma 5, Lemma 6, Lemma 7 and Theorem 2;
    - Section 5.1: the worklist placement of $\varphi$-functions.
