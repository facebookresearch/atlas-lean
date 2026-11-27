# Binary index as a base-2 digit encoding

Let $k$ be a natural number and $y \in \{0,1\}^k$, with $y_j = 1$ meaning true. Let $\varphi$ be the bijection from digit tuples $d = (d_0, \dots, d_{k-1}) \in \{0, 1\}^k$ to $\{0, \dots, 2^k - 1\}$ given by $\varphi(d) = \sum_{j < k} d_j 2^j$. Then $\sum_{j < k,\ y_j = 1} 2^j = \varphi(d)$, where $d_j = 1$ if $y_j$ is true and $d_j = 0$ otherwise.
