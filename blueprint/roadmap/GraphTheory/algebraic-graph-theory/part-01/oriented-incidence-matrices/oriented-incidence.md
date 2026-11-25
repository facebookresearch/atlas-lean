# Oriented incidence matrix of a multigraph

Let $V$ and $E$ be sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a multigraph; loops are allowed). Its oriented incidence matrix is the real $V \times E$ matrix

$$B_{v e} = [e^- = v] - [e^+ = v],$$

so that the column of an edge with distinct endpoints is $+1$ at $e^-$ and $-1$ at $e^+$, and the column of a loop is $0$. Distinct edges, including parallel ones, give distinct columns.
