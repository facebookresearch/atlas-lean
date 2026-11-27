# Round elimination operators on node-edge-checkable problems

A node-edge-checkable problem on $\Delta$-regular graphs (or bipartite $(\Delta, 2)$-biregular graphs) is a triple $\Pi = (\Sigma, \mathcal{N}, \mathcal{E})$ where $\Sigma$ is a finite set of labels, $\mathcal{N}$ is a set of multisets of size $\Delta$ over $\Sigma$ (allowed labels on the half-edges around a node) and $\mathcal{E}$ a set of multisets of size $2$ (allowed labels on the two halves of an edge). The operator $\mathrm{R}$ maps $\Pi$ to the problem $\mathrm{R}(\Pi)$ whose labels are nonempty subsets of $\Sigma$, whose edge constraint consists of pairs $\{A, B\}$ with $\{a, b\} \in \mathcal{E}$ for all $a \in A$, $b \in B$ (taking only maximal such pairs), and whose node constraint consists of multisets $\{A_1, \dots, A_\Delta\}$ for which some choice $a_i \in A_i$ satisfies $\{a_1, \dots, a_\Delta\} \in \mathcal{N}$. The operator $\overline{\mathrm{R}}$ is defined symmetrically with the roles of node and edge constraints exchanged.

## Depends on

- [Locally checkable labeling problem](locally-checkable-labeling-problem.md)

## Sources

- S. Brandt, "An Automatic Speedup Theorem for Distributed Problems", PODC 2019, arXiv:1902.09958.
