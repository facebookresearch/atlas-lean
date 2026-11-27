# Hierarchical clustering of maximum parsimony reconciliations

Because MPR space can be exponentially large and diverse, it is summarized by a clustering $\mathcal C = \{C_1, \dots, C_k\}$ of the MPRs, each cluster represented compactly as a **reconciliation subgraph** (a union of traversals of the reconciliation graph). With $\mu_i$ the average pairwise distance between MPRs of $C_i$ and $\sigma_i$ the average support of the events of $C_i$ (support computed within $C_i$), define

$$\mathrm{WAD}(\mathcal C) = \frac{\sum_i |C_i|\,\mu_i}{\sum_i |C_i|}, \qquad \mathrm{WAS}(\mathcal C) = \frac{\sum_i |C_i|\,\sigma_i}{\sum_i |C_i|} .$$

**Initialization.** Descend $L$ levels from the sources of the reconciliation graph, branching over every event choice; each level-$L$ partial traversal together with all nodes reachable from its leaves is an initial cluster. The smallest $L$ giving at least the desired number $N$ of clusters is used; at full depth the clusters are single MPRs.

**Agglomeration.** Repeatedly merge the pair of clusters whose union most decreases WAD (or most increases WAS), merging their subgraphs.

**Lemmas.** With $n = |V_S|$ and $m = |V_G|$:

1. the reconciliation graph has $O(n^2 m)$ nodes and arcs;
2. the $N$ initial clusters are built in $O(N n^2 m)$ time;
3. clustering by weighted average distance runs in $O(N^2 n^4 m^2 \log m)$ time;
4. clustering by weighted average support runs in $O(N^2 n^2 m)$ time.

Neither bound depends on the number of MPRs.

## Depends on

- [Reconciliation graph of maximum parsimony DTL reconciliations](reconciliation-graph-of-maximum-parsimony-reconciliations.md)
- [Pairwise distance vector of maximum parsimony reconciliations](pairwise-distance-vector-of-maximum-parsimony-reconciliations.md)
- [Median reconciliation and event support](median-reconciliation-and-event-support.md)

## Expansion

Every cluster is a reconciliation subgraph, so its size (number of MPRs) is computed in $O(nm)$ time, its average pairwise distance in $O(n^4 m^2 \log m)$ time by the pairwise distance vector algorithm, and its event supports in $O(n^2 m)$ time. The algorithm evaluates all $O(N^2)$ candidate merges once, then performs $O(N)$ merges, each requiring $O(N)$ re-evaluations against the new cluster, which gives Lemmas 3 and 4. A representative of each cluster, such as its median reconciliation, is then extracted from its subgraph; the ratio of the clustered objective to the unclustered one (the improvement score) indicates whether MPR space has genuine cluster structure.

## Sources

- R. Mawhorter, R. Libeskind-Hadas, "Hierarchical clustering of maximum parsimony reconciliations", BMC Bioinformatics 20:612 (2019), WAD and WAS objectives and Lemmas 1-4, <https://doi.org/10.1186/s12859-019-3223-5>, PMCID PMC6882150.