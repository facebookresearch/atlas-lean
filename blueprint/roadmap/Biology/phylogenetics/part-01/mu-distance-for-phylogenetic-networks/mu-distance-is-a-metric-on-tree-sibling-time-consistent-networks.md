# μ-distance is a metric on tree-sibling time-consistent networks

**Networks.** In a rooted DAG, a *tree node* has in-degree at most $1$ and a *hybrid node* in-degree at least $2$. A *phylogenetic network* on $S = \{1, \dots, n\}$ is a rooted DAG in which no tree node has out-degree $1$, every hybrid node has out-degree $1$ with a tree-node child, and the leaves are bijectively labelled by $S$; it is *semi-binary* if every hybrid node has in-degree exactly $2$. It is *tree-sibling* if every hybrid node has a sibling (a node sharing a parent) that is a tree node, and *time consistent* if there is $\tau : V \to \mathbb{N}$ with $\tau(\text{root}) = 0$, $\tau(u) = \tau(v)$ for every arc $(u,v)$ into a hybrid node and $\tau(u) < \tau(v)$ for every arc into a tree node. Write sbTSTC for semi-binary tree-sibling time-consistent networks.

**μ-representation.** For a node $u$, the μ-vector is $\mu(u) = (m_1(u), \dots, m_n(u)) \in \mathbb{N}^n$, where $m_i(u)$ is the number of distinct directed paths from $u$ to leaf $i$. Then $\mu(i) = \delta(i)$ (the $i$-th unit vector) for a leaf, and $\mu(u) = \sum_{v \text{ child of } u} \mu(v)$ otherwise, so all μ-vectors are computable in polynomial time. The μ-representation $\mu(N)$ is the multiset of the μ-vectors of all nodes of $N$. For networks $N_1, N_2$ on $S$,

$$d_\mu(N_1, N_2) = \big|\, \mu(N_1) \,\triangle\, \mu(N_2) \,\big|,$$

the size of the multiset symmetric difference.

**Theorem.** On sbTSTC phylogenetic networks on $S$, $d_\mu$ is a metric up to isomorphism: $d_\mu \ge 0$; $d_\mu(N_1, N_2) = 0$ iff $N_1 \cong N_2$ (leaf-label-preserving isomorphism); $d_\mu$ is symmetric; and $d_\mu(N_1, N_3) \le d_\mu(N_1, N_2) + d_\mu(N_2, N_3)$. On phylogenetic trees it equals the Robinson–Foulds distance (each non-leaf μ-vector is the indicator of a cluster), and it is also a metric on tree-child networks.

## Depends on

- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)
- [Sibling or quasi-sibling leaves and node-count bounds in tree-sibling time-consistent networks](sibling-or-quasi-sibling-leaves-and-node-count-bounds.md)

## Expansion

Non-negativity, symmetry and the triangle inequality hold for the symmetric-difference size of any multisets, and isomorphic networks have equal μ-representations. Separation is proved by induction on the numbers of leaves and of hybrid nodes. Every sbTSTC network with at least two leaves has a pair of leaves $i, j$ with $j$ a sibling or a quasi-sibling of $i$ (the child of a hybrid node that is a sibling of $i$). Whether $j$ is a sibling or quasi-sibling of $i$, and whether the parent $u$ of $i$ has out-degree $2$, can be read from $\mu(N)$: the pair is sibling or quasi-sibling iff $\mu(u)$ is the least μ-vector dominating $\delta(i) + \delta(j)$ and the μ-vectors strictly between it and $\delta(i)$, resp. $\delta(j)$, are exactly $\{\delta(i)\}$ and $\{\delta(j)\}$ (sibling) or $\{\delta(j), \delta(j)\}$ (quasi-sibling); and $\operatorname{outdeg}(u) = 2$ iff $\mu(u) = \delta(i) + \delta(j)$. Hence two networks with equal μ-representations admit the same one of four reversible reductions (delete a sibling leaf, with or without suppressing its parent; delete the arc from $u$ to the hybrid parent of $j$, with or without suppressing $u$), each of which removes a leaf or a hybrid node and transforms μ-representations by an explicit rule, so the reduced networks again have equal μ-representations; the induction hypothesis makes them isomorphic, and reversing the reduction makes $N_1 \cong N_2$. Without the tree-sibling, time-consistency or semi-binarity conditions, non-isomorphic networks with equal μ-representations exist.

## Sources

- G. Cardona, M. Llabrés, F. Rosselló and G. Valiente, "A distance metric for a class of tree-sibling phylogenetic networks", Bioinformatics 24 (2008), 1481–1488, Sections 2–5 (Lemmas 3–4, Proposition 5, Theorem 6), <https://doi.org/10.1093/bioinformatics/btn231>, PMCID: PMC2718672.
