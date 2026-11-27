# Unions of the first k forests are k-edge-connectivity certificates

For every undirected multigraph $G$ with $n \ge 1$ vertices, every forest decomposition $F_1, F_2, \dots$ of $G$ and every $k \ge 1$, the subgraph $G_k = F_1 \cup \dots \cup F_k$ is a $k$-edge-connectivity certificate of $G$ and has at most $k(n-1)$ edges. In particular $G_k$ preserves every cut of size less than $k$ exactly, and $\lambda(G_k) \ge \min\{\lambda(G), k\}$.

## Proof sketch

The edge bound holds because each forest has at most $n - 1$ edges. For the certificate property use induction on $k$; the case $k = 1$ is the maximality of $F_1$. If $\lambda_{G_{i+1}}(x,y) < \min\{\lambda_G(x,y), i+1\}$ while $\lambda_{G_i}(x,y) \ge \min\{\lambda_G(x,y), i\}$, then $\lambda_G(x,y) \ge i+1$ and there is a set $S$ separating $x$ from $y$ with $|\partial_{G_{i+1}} S| = |\partial_{G_i} S| = i$, so $F_{i+1}$ has no edge in $\partial S$. Since $|\partial_G S| \ge i+1$, some edge $e \in \partial_G S$ lies in $G - E(G_i)$; maximality of $F_{i+1}$ in that graph means the endpoints of $e$ are joined by a path of $F_{i+1}$, which must use an edge of $\partial S$, a contradiction.

## Depends on

- [Sparse k-edge-connectivity certificates and forest decompositions](sparse-k-edge-connectivity-certificate.md)

## Proof depends on

- [Menger's theorem for edge cuts and edge-disjoint paths](../menger-s-theorem/menger-edge-max-min.md)

## Sources

- Hiroshi Nagamochi, Toshihide Ibaraki, "A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph", Algorithmica (1992).
