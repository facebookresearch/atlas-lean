# Blobs and the reduced unrooted tree of blobs of a phylogenetic network

Let $\mathcal{N}^+$ be a rooted binary phylogenetic network on taxon set $X$ (a directed acyclic
graph with root $r$, leaves bijectively labeled by $X$, tree nodes of in-degree $1$ and out-degree $2$,
and hybrid nodes of in-degree $2$ and out-degree $1$), equipped under the network multispecies coalescent
(NMSC) with positive tree-edge lengths $\ell_e > 0$ and hybrid inheritance probabilities
$\gamma_e \in (0, 1)$ summing to $1$ at each hybrid node.

- A **cut edge** is an edge whose deletion increases the number of connected components.
- The **lowest stable ancestor** $\operatorname{LSA}(\mathcal{N}^+)$ is the lowest node lying on every directed path from the root $r$ to every leaf in $X$. Deleting all nodes and edges above $\operatorname{LSA}(\mathcal{N}^+)$ gives the LSA network $\mathcal{N}^\oplus$, and undirecting its tree edges and suppressing any degree-2 root yields the **semidirected unrooted network** $\mathcal{N}^-$.
- A **blob** is a maximal connected subnetwork containing no cut edges. A blob is **trivial** if it is a single node, and is an **$m$-blob** if it has $m$ incident cut edges.
- The **tree of blobs** $T(\mathcal{N}^-)$ is the unrooted tree obtained by contracting every blob of $\mathcal{N}^-$ to a single node. Suppressing all degree-2 nodes in $T(\mathcal{N}^-)$ yields the **reduced unrooted tree of blobs** $T_{\mathrm{rd}}(\mathcal{N}^-)$.
- A 4-taxon subset $\{a, b, c, d\} \subseteq X$ is a **B-quartet** (blob quartet) on $\mathcal{N}^+$ if its induced quartet on $T_{\mathrm{rd}}(\mathcal{N}^-)$ is unresolved (a star), and a **T-quartet** (tree quartet) if it is resolved ($ab|cd$, $ac|bd$, or $ad|bc$).

## Sources

- E. S. Allman, H. Baños, J. D. Mitchell, and J. A. Rhodes, "The tree of blobs of a species network: identifiability under the coalescent", Journal of Mathematical Biology 86 (2023), 10 (published online 2022), <https://doi.org/10.1007/s00285-022-01838-9> (PMC10062380). (Definitions 1–13.)
