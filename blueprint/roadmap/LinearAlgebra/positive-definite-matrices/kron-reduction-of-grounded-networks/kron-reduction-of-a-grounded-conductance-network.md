# Kron reduction of a grounded conductance network

Let $L_w$ be the weighted Laplacian of an arc network with nonnegative conductances $w$ in which a ground node $r$ is joined to
every node by a walk of arcs of positive conductance, so that the grounded matrix $L = L_w^{(r)}$ is
[positive definite](../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/grounded-weighted-laplacian-pos-def.md).
Split the non-ground nodes into nonempty sets $P$ of ports and $I$ of interior nodes and write $L$ in blocks $L_{PP}$, $L_{PI}$,
$L_{IP} = L_{PI}^{\mathsf T}$, $L_{II}$. Then $L_{II}$ is positive definite, the Kron-reduced matrix

$$K = L_{PP} - L_{PI} L_{II}^{-1} L_{IP}$$

is positive definite, and for every injection $j = (j_P, j_I)$ the nodal equations $L \varphi = j$ have exactly one solution,
whose port potentials and interior potentials satisfy

$$K \varphi_P = j_P - L_{PI} L_{II}^{-1} j_I, \qquad \varphi_I = L_{II}^{-1}(j_I - L_{IP}\varphi_P).$$

When $j_I = 0$ the dissipated power is preserved: $\varphi^{\mathsf T} L \varphi = \varphi_P^{\mathsf T} K \varphi_P$. Positive
definiteness of $K$ follows by choosing $\varphi_I = -L_{II}^{-1} L_{IP} \varphi_P$, for which
$\varphi^{\mathsf T} L \varphi = \varphi_P^{\mathsf T} K \varphi_P$.

## Depends on

- [The grounded weighted Laplacian of an arc network is positive definite](../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/grounded-weighted-laplacian-pos-def.md)

## Sources

- F. Dörfler and F. Bullo, "Kron reduction of graphs with applications to electrical networks", *IEEE Transactions on Circuits and Systems I: Regular Papers* 60(1):150–163, 2013.
