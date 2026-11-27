# Round elimination operators on node-edge-checkable problems

A node-edge-checkable problem on graphs of maximum degree $\Delta$ is a triple $\Pi = (\Sigma, \mathcal{N}, \mathcal{E})$ where $\Sigma$ is a finite set of labels, $\mathcal{N}$ is a set of multisets of size at most $\Delta$ over $\Sigma$ and $\mathcal{E}$ a set of multisets of size $2$. A labelling of the half-edges is a solution if the two labels on every edge form a multiset in $\mathcal{E}$ and, at every node $v$ of degree $d(v) \le \Delta$, the $d(v)$ labels on its incident half-edges form a multiset in $\mathcal{N}$ (Brandt, Section 3, where $\mathcal{N}$ and $\mathcal{E}$ are the sets $h(\Delta)$ and $g(\Delta)$). A node of degree $1$, such as an endpoint of a path, is thus checked against the multisets of size $1$ in $\mathcal{N}$; on $\Delta$-regular graphs (or bipartite $(\Delta, 2)$-biregular graphs, on the $\Delta$-side) only the multisets of size exactly $\Delta$ are ever used. The operator $\mathrm{R}$ maps $\Pi$ to the problem $\mathrm{R}(\Pi)$ whose labels are nonempty subsets of $\Sigma$, whose edge constraint consists of pairs $\{A, B\}$ with $\{a, b\} \in \mathcal{E}$ for all $a \in A$, $b \in B$ (taking only maximal such pairs), and whose node constraint consists of the multisets $\{A_1, \dots, A_i\}$ with $i \le \Delta$ for which some choice $a_1 \in A_1, \dots, a_i \in A_i$ satisfies $\{a_1, \dots, a_i\} \in \mathcal{N}$ (Brandt, Section 4.1, the problem $\Pi_{1/2}$, with the maximality pruning of Section 4.2). The operator $\overline{\mathrm{R}}$ is defined symmetrically with the roles of node and edge constraints exchanged.

## Depends on

- [Locally checkable labeling problem](locally-checkable-labeling-problem.md)

## Sources

- S. Brandt, "An Automatic Speedup Theorem for Distributed Problems", PODC 2019, arXiv:1902.09958, Sections 3, 4.1 and 4.2.
