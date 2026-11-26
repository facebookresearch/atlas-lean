# Uniqueness of level-1 networks from induced triplets and softwired clusters

Let $\mathcal L_1(X)$ be the binary level-1 phylogenetic networks on leaf set $X$ (definitions as in the size-bounds entry below), with induced triplet system $\mathcal R(N)$ and softwired cluster system $\mathcal S(N)$. A network $N$ is
- **simple** if it has exactly one gall and every leaf is adjacent to a vertex of that gall;
- **4-outwards** if its underlying graph has no cycle of length four or less;
- **saturated** if no vertex is incident with more than one cut arc.

$N$ is **$\mathcal L_1(X)$-defined** by a triplet system $\mathcal R$ if, up to equivalence, $N$ is the unique network $N' \in \mathcal L_1(X)$ with $\mathcal R \subseteq \mathcal R(N')$; similarly for a cluster system $\mathcal C$ and $\mathcal C \subseteq \mathcal S(N')$. This is stronger than being encoded ($\mathcal R(N') = \mathcal R(N) \Rightarrow N' = N$), which holds exactly for the 4-outwards networks.

**Theorem (simple networks).** Every simple $N \in \mathcal L_1(X)$ with $|X| \ge 4$ is $\mathcal L_1(X)$-defined by a triplet system of size at most $2|X| - 1$, and by a cluster system of size at most $|X|$. In particular it is $\mathcal L_1(X)$-defined by $\mathcal R(N)$ and by $\mathcal S(N)$.

**Theorem (saturated networks).** Every 4-outwards, saturated $N \in \mathcal L_1(X)$ is $\mathcal L_1(X)$-defined by $\mathcal R(N)$ and by $\mathcal S(N)$.

Without saturation the conclusion fails: a 4-outwards network containing a directed path of three or more cut arcs can be modified into a non-equivalent $N'$ with $\mathcal R(N) \subseteq \mathcal R(N')$, and similarly for clusters.

## Expansion

A set $S \subseteq X$ is an **SN-set** of $\mathcal R$ if no triplet $xy|z \in \mathcal R$ has $x, z \in S$ and $y \notin S$; the cluster below every cut arc is an SN-set of $\mathcal R(N)$. If $\mathcal R(N) \subseteq \mathcal R(N')$, the clusters below cut arcs of $N$ and $N'$ are pairwise compatible, so the partition $\mathrm{Cut}(N)$ of $X$ by maximal SN-sets is shared by $N$ and $N'$ when $N$ is saturated. For a simple network, $2|X| - 1$ triplets read around the gall fix the cyclic order of the leaves, the position of the hybrid and the root. For saturated networks the proof is induction on $g(N)$: collapse each part of $\mathrm{Cut}(N)$ to a leaf to get a simple network $\mathrm{Collapse}(N)$, apply the simple case, and recurse into the parts. The cluster version follows because the trees displayed by $N$ have triplets determined by their clusters, so $\mathcal S(N) \subseteq \mathcal S(N')$ implies $\mathcal R(N) \subseteq \mathcal R(N')$. Since real data rarely provide all of $\mathcal R(N)$ or $\mathcal S(N)$, the failure without saturation limits triplet- and cluster-based network reconstruction.

## Depends on

- [Size bounds for binary level-1 networks and their cluster systems](size-bounds-for-binary-level-1-networks-and-their-cluster-systems.md)

## Sources

- P. Gambette, K. T. Huber, S. Kelk, "On the challenge of reconstructing level-1 phylogenetic networks from triplets and clusters", Journal of Mathematical Biology (2017), Observation 1, Proposition 5.1, Theorem 6.1, Corollary 6.2, Theorem 6.3, Theorem 7.1, Corollary 7.2 and Theorem 7.3, <https://doi.org/10.1007/s00285-016-1068-3>, PMCID PMC5420025.
