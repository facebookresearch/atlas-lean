# Cost of a closed tour

For a cost function $d$ on the vertices with values in an additive
commutative monoid, the cost of the closed tour that visits $x_0, x_1, \dots, x_k$ in order and
returns to its first vertex is $\sum_{i=1}^{k} d(x_{i-1}, x_i) + d(x_k, x_0)$. The empty tour
costs $0$.
