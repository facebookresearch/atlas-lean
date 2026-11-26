# Single-input structural controllability through a minimal upstream node set

**Setting.** Consider a directed network of $N$ nodes in which each node $i$ is a single-input single-output linear system with a proper rational transfer function

$$G_i(s) = \frac{n_i(s)}{d_i(s)},$$

where $n_i$ and $d_i$ are generic polynomials of finite but arbitrary (and possibly node-dependent) order: every coefficient up to the order of the polynomial is a free nonzero parameter. Node $i$ is driven by the weighted sum of the outputs of its in-neighbours plus any external inputs, $X_i(s) = G_i(s)\big[\sum_k a_{ik}X_k(s) + \sum_j b_{ij}U_j(s)\big]$.

**Upstream node set.** Call a set $D$ of nodes an upstream set if every node of the network is downstream of (reachable by a directed path from) at least one node of $D$; the source paper calls a minimum such set the power dominating set (PDS). Attach a single control node carrying the input $u$ to every node of a minimum upstream set $D$. In the augmented graph every node is downstream of the control node. A *structural control network* is a directed spanning tree of the augmented graph rooted at the control node.

**Proposition (one input at the upstream set).** Under these hypotheses the network is structurally controllable with one independent input ($N_D = 1$) connected to a minimum upstream set $D$. Connecting the input(s) to at least an upstream set is also necessary for controllability, since a node not downstream of any input cannot be influenced.

**Remark.** A node set is upstream iff it meets every source strongly connected component of the graph (a strongly connected component with no incoming edge from outside), so a minimum upstream set consists of one node from each source component.

## Expansion

Structural controllability again needs only one controllable parameter choice. Delete every edge not in the structural control network and set the tree edges to $1$. The tree has no cycles and a unique path from $u$ to each node $j$; with $\mathcal J_j$ the nodes on that path, the transfer function from $u$ to node $j$ is

$$H_j(s) = \frac{X_j(s)}{U(s)} = \prod_{k\in\mathcal J_j} G_k(s), \qquad j = 1,\dots,N.$$

Now use the freedom in the polynomial coefficients: choose the denominators so that no pole is repeated anywhere in the network, and the numerators so that no pole-zero cancellation occurs along any root-to-node path. A minimal realization of the input-to-all-states map then needs exactly one eigenvalue for each network pole, and the number of eigenvalues of a minimal realization equals the number that are both controllable and observable. Hence every state is controllable for this parameter choice, and Lin's theorem gives structural controllability.

This extends the first-order case (where each node has $G_i(s) = 1/(s+p_i)$ and one input feeding all nodes already suffices) to arbitrary-order nodal dynamics and shows that the input need only touch the upstream set, which for many biological networks is small.

## Depends on

- [Single-input structural controllability of networks with nodal time constants](single-input-structural-controllability-with-nodal-time-constants.md)

## Sources

- N. J. Cowan, E. J. Chastain, D. A. Vilhena, J. S. Freudenberg, C. T. Bergstrom, "Nodal dynamics, not degree distributions, determine the structural controllability of complex networks", PLoS ONE 7(6) (2012) e38398, Definition 1, Proposition 2, Equation (5) and Figure 1, <https://doi.org/10.1371/journal.pone.0038398>, PMCID PMC3382243.
