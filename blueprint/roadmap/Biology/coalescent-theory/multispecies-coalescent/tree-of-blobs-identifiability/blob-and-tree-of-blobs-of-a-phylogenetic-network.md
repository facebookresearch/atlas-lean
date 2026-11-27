# Blobs and the reduced unrooted tree of blobs of a phylogenetic network

Let $\mathcal{N}^+$ be a rooted binary phylogenetic network on taxon set $X$: a connected directed acyclic graph
with a root $r$ of in-degree $0$ and out-degree $2$, leaves of in-degree $1$ and out-degree $0$ labeled
bijectively by $X$, tree nodes of in-degree $1$ and out-degree $2$, and hybrid nodes of in-degree $2$ and
out-degree $1$. An edge is a hybrid edge if its child is a hybrid node and a tree edge otherwise. The
definitions below are topological; under the network multispecies coalescent (NMSC) the network is also
metric, with lengths $\ell_e > 0$ on tree edges, lengths $\ell_e \ge 0$ on hybrid edges, and hybridization
parameters $\gamma_e > 0$ on hybrid edges summing to $1$ over the two hybrid edges at each hybrid node.

- A **cut edge** is an edge whose deletion increases the number of connected components of the underlying
  undirected graph.
- The **lowest stable ancestor** $\operatorname{LSA}(\mathcal{N}^+)$ is the node, among those lying on every directed path from $r$ to a leaf, that lies below all the others. Deleting all nodes and edges above it and designating it as the root gives the LSA network $\mathcal{N}^\oplus$; undirecting its tree edges, keeping the directions of its hybrid edges, and suppressing its root gives the **semidirected unrooted network** $\mathcal{N}^-$.
- A **blob** is a maximal connected subnetwork containing no cut edge, and it is **trivial** if it is a single node. An edge is incident to a blob if exactly one of its endpoints lies in the blob.
- A blob of a rooted network such as $\mathcal{N}^+$ or $\mathcal{N}^\oplus$ is an **$m$-blob** if it has exactly $m$ incident cut edges and does not contain the root, or exactly $m - 1$ incident cut edges and contains the root. So the root of a rooted binary tree, with two incident cut edges, is a trivial $3$-blob. A blob of the unrooted network $\mathcal{N}^-$ is an $m$-blob if it has exactly $m$ incident cut edges.
- The **tree of blobs** $T(\mathcal{N}^-)$ is the unrooted tree obtained by contracting every blob of $\mathcal{N}^-$ to a single node. Suppressing all degree-2 nodes of $T(\mathcal{N}^-)$ yields the **reduced unrooted tree of blobs** $T_{\mathrm{rd}}(\mathcal{N}^-)$.
- A 4-taxon subset $\{a, b, c, d\} \subseteq X$ is a **B-quartet** (blob quartet) on $\mathcal{N}^+$ if its induced quartet on $T_{\mathrm{rd}}(\mathcal{N}^-)$ is unresolved (a star), equivalently if deleting the cut edges incident to some blob leaves $a, b, c, d$ in four distinct connected components; otherwise it is a **T-quartet** (tree quartet), and its induced quartet is resolved ($ab|cd$, $ac|bd$, or $ad|bc$).

## Sources

- E. S. Allman, H. Baños, J. D. Mitchell, and J. A. Rhodes, "The tree of blobs of a species network: identifiability under the coalescent", Journal of Mathematical Biology 86 (2023), 10 (published online 2022), <https://doi.org/10.1007/s00285-022-01838-9> (PMC10062380). (Definitions 1–13.)
