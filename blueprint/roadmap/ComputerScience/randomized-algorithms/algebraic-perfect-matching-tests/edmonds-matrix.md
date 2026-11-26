# The Edmonds matrix of a bipartite graph

Let $G$ be a bipartite graph with left and right vertex sets both indexed by $\{1, \dots, n\}$. Its **Edmonds matrix** is the $n \times n$ matrix $E_G$ over the polynomial ring $\mathbb{Z}[x_{ij} : 1 \le i, j \le n]$ with $(E_G)_{ij} = x_{ij}$ if $ij$ is an edge and $0$ otherwise. Its determinant is a polynomial of total degree at most $n$.

## Sources

- J. Edmonds, "Systems of Distinct Representatives and Linear Algebra", Journal of Research of the National Bureau of Standards, Section B 71B(4), 1967.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
