# Oriented incidence matrix of a multigraph

Let $V$ and $E$ be sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a multigraph; loops are allowed). Its oriented incidence matrix is the real $V \times E$ matrix

$$B_{v e} = [e^- = v] - [e^+ = v],$$

so that the column of an edge with distinct endpoints is $+1$ at $e^-$ and $-1$ at $e^+$, and the column of a loop is $0$. Distinct edges, including parallel ones, give distinct columns.

The opposite sign convention is also in use: for arc networks with tail map $t$ and head map $h$, the incidence matrix $\bigl[h(e) = v\bigr] - \bigl[t(e) = v\bigr]$ is $+1$ at the head and $-1$ at the tail, so that multiplying it by a flow gives incoming minus outgoing flow at each vertex. It is the oriented incidence matrix above with the endpoints exchanged: the arc-network incidence matrix of $(t, h)$ equals the oriented incidence matrix of $(e^-, e^+) = (h, t)$. For one arc $a \to b$ with rows ordered $a, b$, the column is $(1, -1)$ in the convention above and $(-1, 1)$ in the arc-network convention.
