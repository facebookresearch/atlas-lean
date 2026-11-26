# Tree-, cluster- and tripartition-based dissimilarities of networks

Let $N_1, N_2$ be rooted phylogenetic networks on the same taxon set $X$, with root $r_i$ and arc set $E(N_i)$. An arc $(u, v)$ of a tree or network is *internal* if its head $v$ is not a leaf. For each network let $\mathcal{T}(N_i)$ be its set of displayed trees.

- **Clusters.** For a rooted tree $T$ on $X$, an arc $e = (u, v)$ induces the cluster $c_e$ of leaves below $v$, and the (nontrivial) clusters of $T$ are $\mathcal{C}(T) = \{c_e : e \text{ an internal arc of } T\}$. The cluster set of $N_i$ is $\mathcal{C}_i = \bigcup_{T \in \mathcal{T}(N_i)} \mathcal{C}(T)$. Singleton clusters (pendant arcs) and the full set $X$ (no arc enters the root) are not included.
- **Tripartitions.** For an arc $e = (u, v)$ of $N_i$, put $A_e = \{x \in X : \text{every path from } r_i \text{ to } x \text{ passes through } v\}$, $B_e = \{x \in X : \text{some, but not every, path from } r_i \text{ to } x \text{ passes through } v\}$ and $C_e = X \setminus (A_e \cup B_e)$, and let $\theta_e = (A_e, B_e, C_e)$. Reachability is through the head vertex $v$, not through the arc $e$: at a reticulation $v$ the two incoming arcs have the same tripartition. The tripartition set is $\theta_i = \{\theta_e : e \text{ an internal arc of } N_i\}$.

**Cluster-based measure.** When $\mathcal{C}_1$ and $\mathcal{C}_2$ are both nonempty,

$$m_{\mathrm{cluster}}(N_1, N_2) = \frac{1}{2}\left(\frac{|\mathcal{C}_1 \setminus \mathcal{C}_2|}{|\mathcal{C}_1|} + \frac{|\mathcal{C}_2 \setminus \mathcal{C}_1|}{|\mathcal{C}_2|}\right).$$

**Tripartition-based measure.** When $\theta_1$ and $\theta_2$ are both nonempty,

$$m_{\mathrm{tripartition}}(N_1, N_2) = \frac{1}{2}\left(\frac{|\theta_1 \setminus \theta_2|}{|\theta_1|} + \frac{|\theta_2 \setminus \theta_1|}{|\theta_2|}\right).$$

The empty cases (for example a network whose displayed trees are all stars, which has no internal arcs) are excluded: the measures are not defined there.

**Tree-based measure.** Let $d$ be a symmetric function on pairs of trees with $d(T, T) = 0$, such as the Robinson–Foulds distance. Form the complete bipartite graph with parts $\mathcal{T}(N_1)$ and $\mathcal{T}(N_2)$ and edge weights $w(T, T') = d(T, T')$. Minimum-weight edge covers (sets of edges touching every vertex, of least total weight) need not be unique, and different ones can have different sizes, so the average weight is fixed by a convention: let $C$ be a minimum-weight edge cover of least cardinality among the minimum-weight edge covers. Since both the total weight and $|C|$ are then determined,

$$m_{\mathrm{tree}}(N_1, N_2) = \frac{\sum_{e \in C} w(e)}{|C|}$$

does not depend on the choice of $C$. This tie rule is a convention of this page; the source's definition does not resolve ties.

All three measures vanish when $N_1 = N_2$ and are symmetric, but none is a metric on the class of all rooted networks: two non-isomorphic networks can display the same trees and clusters, and so be at tree- and cluster-distance $0$.

## Depends on

- [Robinson–Foulds distance](../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Proof depends on

- [Robinson–Foulds distance from a tree to itself is zero](../splits-compatibility-ultrametrics-and-upgma/rf-dist-self.md)
- [Symmetry of the Robinson–Foulds distance](../splits-compatibility-ultrametrics-and-upgma/rf-dist-comm.md)

## Expansion

For two different rooted binary triplets, each has a single nontrivial cluster, so each cluster set is a singleton not shared by the other and the cluster measure is $1$; counting the singleton leaves and the full set as clusters would add four shared clusters and give $1/5$, which is why only internal arcs count. Without a tie rule the tree measure is not a function: for displayed-tree sets $\{a, b\}$ and $\{b, c\}$ with $d(a, b) = d(b, c) = 1$ and $d(a, c) = 2$, both $\{(a, b), (b, c)\}$ and $\{(a, b), (b, b), (b, c)\}$ are minimum-weight covers, with averages $1$ and $2/3$. For $N_1 = N_2$ the cover pairing each tree with itself has weight $0$; for $d = d_{RF}$ this is $d_{RF}(T, T) = 0$, and symmetry of $d_{RF}$ gives symmetry of the tree measure, as the definitions of the other two measures are symmetric in $N_1, N_2$. When both networks are trees, the cluster and tripartition measures reduce to normalized Robinson–Foulds-type counts of unshared clusters, and the tree-based measure reduces to $d(N_1, N_2)$. The tripartition measure sees the arcs of the network directly and is computable in polynomial time; the tree- and cluster-based measures enumerate the displayed trees, which can be exponentially many in the number of reticulations. Which measure is appropriate depends on what the network is meant to summarize: a collection of gene trees (tree- or cluster-based) or an ancestry graph up to isomorphism (tripartition-based).

## Sources

- C. Than, D. Ruths and L. Nakhleh, "PhyloNet: a software package for analyzing and reconstructing reticulate evolutionary relationships", BMC Bioinformatics 9 (2008), 322, <https://doi.org/10.1186/1471-2105-9-322>, PMCID PMC2533029. Sections "Tree-based comparison", "Cluster-based comparison", "Tripartition-based comparison" and "Which measure to use?"; Tables 1–2.
