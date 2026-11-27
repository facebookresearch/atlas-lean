# Steffen's circular flow conjecture is false

It is not the case that for every natural number $t > 1$, every $(2t+1)$-graph $M$ on finite vertex and edge sets (loopless, parallel edges allowed; every vertex on exactly $2t + 1$ edges and at least $2t + 1$ edges leaving every vertex set of odd size) has a nowhere-zero $r$-flow for some real $r$, and its circular flow number, the totalised real infimum of the $r$ for which it has a nowhere-zero $r$-flow, is at most $2 + 2/t$. A nowhere-zero $r$-flow is an orientation of the edges with real values $\varphi(e)$, $1 \le |\varphi(e)| \le r - 1$, whose sums into and out of every vertex agree. That is, the proposition [Steffen's conjecture on circular flow numbers of $(2t+1)$-graphs](circular-flow-odd-regular-graphs.md) is false.

As in the [flow definition](has-nowhere-zero-flow.md), values are tested only on the edges, so the published restriction $r \ge 2$ is automatic for graphs with an edge; the empty multigraph is a $(2t+1)$-graph for which every real $r$ is admissible, a set with no infimum; the totalised infimum returns $0$ for it by convention, while the published definition only considers $r \ge 2$. The published counterexamples are nonempty.

## Sources

- Open Problem Garden, Circular flow numbers of r-graphs, http://www.openproblemgarden.org/op/circular_flow_numbers_of_r_graphs.
- D. Mattiolo and E. Steffen, Edge colorings and circular flows on regular graphs, J. Graph Theory 99 (2022), 399–413, arXiv:2001.02484, https://doi.org/10.1002/jgt.22746.
