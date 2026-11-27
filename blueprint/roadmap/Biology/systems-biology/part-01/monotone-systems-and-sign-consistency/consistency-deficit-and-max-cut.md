# Consistency deficit and MAX-CUT

**Definition.** For a signed graph $G$ with edge set $E$ (for example the species graph of a biochemical system), the consistency deficit $\mathrm{CD}(G)$ is the smallest number of edges whose removal leaves a graph with a consistent spin assignment, that is, the species graph of a monotone system.

**Proposition.**
1. *Spin form.* $\mathrm{CD}(G) = \min_\sigma I(\sigma)$, where $I(\sigma)$ is the number of edges inconsistent with the spin assignment $\sigma$.
2. *Partition form.* Writing $A_{+1}$ and $A_{-1}$ for the nodes of spin $+1$ and $-1$,

$$\mathrm{CD}(G) = \min_{(A_{+1}, A_{-1})} \bigl(n_{+1} + n_{-1} + p\bigr),$$

where $n_{\pm 1}$ is the number of negative edges inside $A_{\pm 1}$ and $p$ the number of positive edges between $A_{+1}$ and $A_{-1}$.
3. *Ising form.* With $J_{ij} \in \{\pm 1\}$ the edge labels, the spin-glass energy $H(\sigma) = -\sum_{(j \to i) \in E} J_{ij}\sigma_i\sigma_j$ equals $I(\sigma) - C(\sigma)$, where $C(\sigma) = |E| - I(\sigma)$ counts consistent edges, so ground states of $H$ are exactly the minimizers of $I$, and $G$ is consistent if and only if the model is unfrustrated.
4. *MAX-CUT.* If every edge is negative, $\mathrm{CD}(G) = |E| - \mathrm{maxcut}(G)$. Conversely, replacing each positive edge $v_i \to v_j$ by a new node $w_{ij}$ and two negative edges $v_i \to w_{ij} \to v_j$ preserves the consistency deficit, so computing $\mathrm{CD}$ is equivalent to MAX-CUT and is NP-hard. A semidefinite-programming relaxation in the style of Goemans and Williamson finds in polynomial time a spin assignment whose number $C(\sigma)$ of consistent edges is at least $0.878$ times the maximum $|E| - \mathrm{CD}(G)$; the guarantee concerns this maximization, not the deficit $\mathrm{CD}(G)$ itself.

## Expansion

Removing all edges inconsistent with some $\sigma$ leaves a consistent graph, and any consistent subgraph has a consistent $\sigma$ whose inconsistent edges in $G$ are among those removed; this gives item 1, and item 2 just counts those edges by type. In item 3, $J_{ij}\sigma_i\sigma_j$ is $+1$ on consistent and $-1$ on inconsistent edges. In item 4 with all edges negative, the inconsistent edges are those inside a part, so minimizing them maximizes the edges across the cut. For the subdivision, given spins of $v_i, v_j$: if equal, choosing $w_{ij}$ of the opposite spin makes both new edges consistent; if different, exactly one of the two is inconsistent for either spin of $w_{ij}$. So each optimal count is unchanged. Applying a MAX-CUT approximation directly to the enlarged graph degrades the ratio, so the approximation algorithm needs a dedicated construction.

Small deficits suggest that real networks are close to monotone. The yeast transcriptional network of $690$ genes and $1{,}082$ regulatory edges ($221$ negative) has $\mathrm{CD} = 41$ by an exact algorithm (the approximation gave $43$): deleting under $4\%$ of edges makes it consistent, with every component remaining connected. Random graphs with the same node, edge and negative-edge counts need $136.6 \pm 5$ deletions (about $12.6\%$), roughly $15$ standard deviations more. Randomly flipping the signs of $50$ positive and $50$ negative edges raises the deficit to $88.3 \pm 7.1$, so both topology and sign pattern contribute. A small deficit also means the system can be written as a monotone system with few inconsistent feedback connections pulled out as external inputs, which is the setting of decomposition-based analysis.

## Depends on

- [Balanced species graphs and orthant monotonicity](balanced-species-graphs-and-orthant-monotonicity.md)

## Sources

- E. D. Sontag, "Monotone and near-monotone biochemical networks", Systems and Synthetic Biology 1 (2007) 59 to 87, sections "Removing the smallest number of edges so as to achieve consistency", "Relation to Ising spin-glass models", "Some evidence suggesting near-monotonicity of natural networks" and "Decomposing systems into monotone components", <https://doi.org/10.1007/s11693-007-9005-9>, PMCID PMC2533521.
