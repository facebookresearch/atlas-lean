# Converging paths and join sets

Let $G$ be a control-flow graph. Nonnull paths $p : X_0 \to \dots \to X_J$ and $q : Y_0 \to \dots \to Y_K$ in $G$ *converge* at a node $Z$ if

1. $X_0 \ne Y_0$;
2. $X_J = Z = Y_K$;
3. $X_j = Y_k$ implies $j = J$ or $k = K$.

One of the paths may pass through $Z$ more than once, as a cycle through $Z$ does. For a set $S$ of nodes, the *join set* $J(S)$ is the set of nodes $Z$ at which two nonnull paths starting at two distinct nodes of $S$ converge. The *iterated join* $J^+(S)$ is the limit of the increasing sequence $J_1 = J(S)$, $J_{i+1} = J(S \cup J_i)$.

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 2 (the definition of convergence, conditions (1)–(3)) and Section 4.3 (join sets and iterated joins).
