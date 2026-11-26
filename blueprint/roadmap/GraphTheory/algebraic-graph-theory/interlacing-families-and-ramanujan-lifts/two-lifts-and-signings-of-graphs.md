# Two-lifts and signings of a graph

A *signing* of a graph $G = (V, E)$ is a function $s : E \to \{\pm 1\}$; its *signed adjacency matrix* $A_s$ has $(A_s)_{uv} = s(\{u,v\})$ for edges and $0$ otherwise. The *$2$-lift* $\hat G_s$ has vertex set $V \times \{0, 1\}$, and each edge $\{u, v\}$ gives the two edges $\{(u, i), (v, i)\}$ if $s(\{u,v\}) = 1$ and $\{(u, i), (v, 1 - i)\}$ if $s(\{u,v\}) = -1$. Every $2$-lift of a $d$-regular bipartite graph is $d$-regular bipartite with twice as many vertices.

## Sources

- Yonatan Bilu, Nathan Linial, "Lifts, discrepancy and nearly optimal spectral gap", Combinatorica 26(5) (2006).
- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Interlacing families I: bipartite Ramanujan graphs of all degrees", Annals of Mathematics 182(1) (2015); arXiv:1304.4132.
