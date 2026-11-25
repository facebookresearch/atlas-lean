# Epidemic percolation network for SIR epidemics

This node covers the following result. Consider a stochastic SIR epidemic in a closed population of $n$ individuals specified by importation times $t^0_i \in [0, \infty]$, recovery periods $r_i$ and infectious contact intervals $\tau_{ij} \in (0, \infty]$, where $\tau_{ij}$ is the time from the infection of $i$ to its infectious contact with $j$ ($\infty$ if there is none), and assume that finite infectious contact times are never tied. Assume time homogeneity: the recovery periods do not depend on the importation times or on the history of the epidemic, and the distribution of the matrix $\tau$ does not depend on them either. The epidemic percolation network of $\tau$ has a directed edge $i \to j$ when $\tau_{ij} < \infty$ and $\tau_{ji} = \infty$, and an undirected edge between $i$ and $j$ when $\tau_{ij} < \infty$ and $\tau_{ji} < \infty$. Then a node is infected if and only if it lies in the out-component of some node $i$ with $t^0_i < \infty$; hence the final outcome of the epidemic depends only on the set of imported infections and the epidemic percolation network.

## Expansion

A good expansion replaces this node by planned pages beside it, each citing the source below:

1. The closed-population SIR model specified by importation times, recovery periods and infectious contact intervals, with the infection algorithm and the no-ties assumption.
2. The time-homogeneity assumptions.
3. Semidirected networks, out-components and the epidemic percolation network of a contact-interval matrix.
4. The statement that the infected nodes are exactly the out-component of the imported infections.

The source also states large-population limits (self-limited outbreak sizes follow the small out-component sizes; the epidemic threshold is the appearance of a giant strongly connected component); these are separate claims with their own regimes and are not part of this node.

Nothing beyond the statement above is claimed here.

## Sources

- E. Kenah and J. M. Robins, Second look at the spread of epidemics on networks, Phys. Rev. E 76 (2007), 036113. <https://doi.org/10.1103/PhysRevE.76.036113>
