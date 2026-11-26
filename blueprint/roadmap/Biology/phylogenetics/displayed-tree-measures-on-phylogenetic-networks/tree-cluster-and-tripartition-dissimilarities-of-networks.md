# Tree-, cluster- and tripartition-based dissimilarities of networks

Let $N_1, N_2$ be rooted phylogenetic networks on the same taxon set. For each network let $\mathcal{T}(N_i)$ be its set of displayed trees, $\mathcal{C}_i$ its set of clusters (leaf sets below the vertices of its displayed trees) and $\theta_i$ its set of tripartitions (one per arc, recording the leaves reachable only through the arc, the leaves reachable both through it and otherwise, and the remaining leaves).

**Cluster-based measure.**

$$m_{\mathrm{cluster}}(N_1, N_2) = \frac{1}{2}\left(\frac{|\mathcal{C}_1 \setminus \mathcal{C}_2|}{|\mathcal{C}_1|} + \frac{|\mathcal{C}_2 \setminus \mathcal{C}_1|}{|\mathcal{C}_2|}\right).$$

**Tripartition-based measure.**

$$m_{\mathrm{tripartition}}(N_1, N_2) = \frac{1}{2}\left(\frac{|\theta_1 \setminus \theta_2|}{|\theta_1|} + \frac{|\theta_2 \setminus \theta_1|}{|\theta_2|}\right).$$

**Tree-based measure.** Let $d$ be a distance on trees, such as the Robinson–Foulds distance. Form the complete bipartite graph with parts $\mathcal{T}(N_1)$ and $\mathcal{T}(N_2)$ and edge weights $w(T, T') = d(T, T')$. If $C$ is a minimum-weight edge cover (a set of edges touching every vertex, of least total weight), then

$$m_{\mathrm{tree}}(N_1, N_2) = \frac{\sum_{e \in C} w(e)}{|C|}.$$

All three measures vanish when $N_1 = N_2$ and are symmetric, but none is a metric on the class of all rooted networks: two non-isomorphic networks can display the same trees and clusters, and so be at tree- and cluster-distance $0$.

## Depends on

- [Robinson–Foulds distance](../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

When both networks are trees, the cluster and tripartition measures reduce to normalized Robinson–Foulds-type counts of unshared clusters or edges, and the tree-based measure reduces to $d(N_1, N_2)$. The tripartition measure sees the arcs of the network directly and is computable in polynomial time; the tree- and cluster-based measures enumerate the displayed trees, which can be exponentially many in the number of reticulations. Which measure is appropriate depends on what the network is meant to summarize: a collection of gene trees (tree- or cluster-based) or an ancestry graph up to isomorphism (tripartition-based).

## Sources

- C. Than, D. Ruths and L. Nakhleh, "PhyloNet: a software package for analyzing and reconstructing reticulate evolutionary relationships", BMC Bioinformatics 9 (2008), 322, <https://doi.org/10.1186/1471-2105-9-322>, PMCID PMC2533029. Sections "Tree-based comparison", "Cluster-based comparison", "Tripartition-based comparison" and "Which measure to use?".
