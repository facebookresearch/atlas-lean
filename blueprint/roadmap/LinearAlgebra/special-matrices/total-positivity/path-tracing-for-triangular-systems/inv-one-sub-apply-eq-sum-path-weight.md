# Wright's path-tracing rule

Let $n \in \mathbb{N}$, $R$ a commutative ring and $B$ an $n \times n$ matrix over $R$ indexed by $\{0, \dots, n-1\}$ that is strictly lower triangular ($B_{ij} = 0$ whenever $i \le j$). Then for all $i, j$,

$$\big((I - B)^{-1}\big)_{ij} = \sum_{p \in \mathcal{P}(j, i)} B_{v_1 v_0} B_{v_2 v_1} \cdots B_{v_k v_{k-1}},$$

the sum over the set $\mathcal{P}(j, i)$ of strictly increasing lists of nodes that start at $j$ and end at $i$ (one for each set $S$ with $\{j, i\} \subseteq S \subseteq [j, i]$, listed in increasing order), of the products of the coefficients $B_{vu}$ along consecutive nodes $u, v$ of $p = [v_0, \dots, v_k]$. Here $(I - B)^{-1}$ is the matrix inverse ($I - B$ is invertible, being unitriangular). Reading $B_{uv}$ as the coefficient of the edge $v \to u$ of a directed acyclic graph, the entry is the sum over directed paths from $j$ to $i$ of the path products (only directed paths have nonzero weight).

## Sources

- S. Wright, The method of path coefficients, *Ann. Math. Statist.* 5 (1934), 161–215.
- R. J. Evans, *Graphical Models*, lecture notes, University of Oxford, Chapter 8, §8.6.
