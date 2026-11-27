# Edge-based μ-distance for semidirected tree-child phylogenetic networks

**Semidirected networks.** A semidirected phylogenetic network $N$ is what remains of a rooted phylogenetic network (a DAG with hybrid nodes of in-degree $\ge 2$) when the root position is forgotten: hybrid edges stay directed, tree edges become undirected. Equivalently it is a semidirected acyclic graph that admits **rooted partners**, DAGs obtained by choosing a root in each root component and orienting the undirected edges away from it; these are the generalization of unrooted trees appropriate when reticulations (hybridization, introgression) are identifiable but the root is not. Leaves carry labels in an ordered list $\mathcal L = (\ell_1, \dots, \ell_n)$. $N$ is *strongly tree-child* if every rooted partner is tree-child (every internal node has a child that is a tree node). For a node $v$ of a DAG $G$, the $\mu$-vector $\mu(v,G) \in \mathbb{Z}_{\ge0}^n$ counts directed paths from $v$ to each leaf.

**Rooting invariance.** If $v$ lies in the directed part of $N$ (reachable by directed edges), the set of directed paths from $v$, hence $\mu(v,N)$, is the same in every rooted partner. If $uv$ is an undirected edge, the directed paths starting with $u \to v$ are the same in every rooted partner that orients $uv$ as $(u,v)$, and such a partner always exists; this defines the directional $\mu$-vector $\mu_d(u,v)$. Each root component $T$ has a root $\mu$-vector $\mu_r(T)$ independent of where in $T$ the root is placed.

**Edge-based $\mu$-representation.** For a complete $\mathcal L$-network $N$, let

$$\mu_E(N) = \big\{\!\!\big\{\, \{(\mu(v), t_e)\} : e = (u,v) \text{ directed} \,\big\}\!\!\big\} + \big\{\!\!\big\{\, \{(\mu_d(u,v), \mathrm{tree}), (\mu_d(v,u), \mathrm{tree})\} : e = uv \text{ undirected} \,\big\}\!\!\big\} + \big\{\!\!\big\{\, \{(\mu_r(T), \mathrm{root})\} : T \text{ root component} \,\big\}\!\!\big\},$$

a multiset of tagged vector sets ($t_e$ records whether a directed edge is a tree or hybrid edge), and $d_{\mu_E}(N_1,N_2) = |\mu_E(N_1)\,\triangle\,\mu_E(N_2)|$ the size of the multiset symmetric difference.

**Theorem.** Let $N_1, N_2$ be strongly tree-child $\mathcal L$-networks. Then $\mu_E(N_1) = \mu_E(N_2)$ if and only if $N_1$ and $N_2$ are phylogenetically isomorphic (isomorphic after completion, preserving leaf labels and edge directions up to rootings). Consequently $d_{\mu_E}$ is a metric on the class of complete strongly tree-child $\mathcal L$-networks.

**Size bound.** A tree-child $\mathcal L$-network with $n$ leaves and $t$ root components has at most $n - t$ hybrid nodes, and if it has no elementary nodes, $|V| \le (m+2)(n-t) + t$ and $|E| \le (2m+1)(n-t)$, with $m$ the maximum hybrid in-degree; so $\mu_E(N)$ has polynomial size and $d_{\mu_E}$ is computable in polynomial time.

## Expansion

For rooted tree-child networks, Cardona et al. showed that the multiset of node $\mu$-vectors determines the network; the difficulty in the semidirected case is that path counts depend on the unknown root. The resolution is that along directed (hybrid) parts nothing depends on the root, and along an undirected edge only its orientation matters, so recording both orientations of every undirected edge gives a root-free invariant. Strong tree-childness guarantees that every rooted partner has the reconstruction property and that the $\mu$-vectors of different root components are incomparable, so the multiset can be decoded back into the network.

## Sources

- Michael Maxfield, Jingcheng Xu and Cécile Ané, "A Dissimilarity Measure for Semidirected Networks", IEEE Transactions on Computational Biology and Bioinformatics 22 (2025), 684–696, <https://doi.org/10.1109/tcbbio.2025.3534780>; numbering as in arXiv:2405.16035: Definitions of semidirected tree-child networks, directional and root $\mu$-vectors and the edge-based $\mu$-representation; Propositions 15, 16, 19, 20 and 24; Theorems 1 and 2.
