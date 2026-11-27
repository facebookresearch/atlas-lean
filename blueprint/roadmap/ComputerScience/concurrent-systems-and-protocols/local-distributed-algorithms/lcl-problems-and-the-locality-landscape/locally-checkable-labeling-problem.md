# Locally checkable labeling problem

Fix integers $\Delta, r \ge 1$ and finite sets $\Sigma_{\mathrm{in}}, \Sigma_{\mathrm{out}}$. Labels are attached both to vertices and to half-edges, the incidences $(v, e)$ of a vertex $v$ with an incident edge $e$. A locally checkable labeling (LCL) problem $\Pi$ on graphs of maximum degree at most $\Delta$ is specified by a finite set $\mathcal{C}$ of allowed centred configurations: isomorphism classes of graphs of radius at most $r$ around a distinguished centre, with maximum degree $\Delta$, whose vertices and half-edges carry input labels from $\Sigma_{\mathrm{in}}$ and output labels from $\Sigma_{\mathrm{out}}$, isomorphisms preserving the centre, the incidence structure and all labels. An output labeling $\lambda$ of the vertices and half-edges of an input-labelled graph $G$ is a solution if for every vertex $v$ the radius-$r$ neighbourhood of $v$, centred at $v$ and with its labels, belongs to $\mathcal{C}$. Examples using vertex labels only are proper $k$-colouring and maximal independent set. Half-edge labels let a vertex designate particular incident edges: maximal matching labels each half-edge matched or unmatched, requiring the two halves of an edge to agree, at most one matched edge at each vertex, and a matched edge at every neighbour of an unmatched vertex; sinkless orientation labels the two halves of every edge tail and head, one each, and requires a tail at every vertex.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- M. Naor, L. Stockmeyer, "What Can Be Computed Locally?", SIAM Journal on Computing 24(6) (1995); STOC 1993.
