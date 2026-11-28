# Characterization of PDT graphs and hardness of EDT recognition

**Setting.** Let $\mathscr{S} = (T, S, \sigma, \mu, \tau_T, \tau_S)$ be a relaxed scenario (dated gene tree, dated species tree, leaf coloring $\sigma : L(T) \to L(S)$ and time-consistent reconciliation map, with horizontal transfers allowed). The *prior-divergence-time* (PDT) graph has an edge $xy$ when $\tau_T(\mathrm{lca}_T(x,y)) > \tau_S(\mathrm{lca}_S(\sigma(x),\sigma(y)))$, and the *equal-divergence-time* (EDT) graph has an edge $xy$ when the two times are equal. A vertex-colored graph $(G,\sigma)$ is a PDT (resp. EDT) graph if some relaxed scenario has it as its PDT (resp. EDT) graph. A set $\mathscr{R}$ of rooted triples is consistent if some tree displays all of them.

**Theorem (PDT graphs).** $(G,\sigma)$ is a PDT graph if and only if

1. $G$ is a cograph,
2. the complement $(\overline{G},\sigma)$ is properly colored, and
3. the triple set $R(G) = \{\sigma(x)\sigma(y)|\sigma(z) : xy \in E(G),\ xz, yz \notin E(G),\ \sigma(x),\sigma(y),\sigma(z) \text{ pairwise distinct}\}$ is consistent.

PDT graphs can therefore be recognized, and an explaining scenario constructed, in polynomial time.

**Theorem (HGT-free EDT graphs).** Let $\mathscr{R}$ contain $\sigma(x)\sigma(y)|\sigma(z)$ whenever $xz, yz \in E$ and $xy \notin E$ for some $x,y,z$ of pairwise distinct colors. Then $(G = (L,E),\sigma)$ is an EDT graph explained by a relaxed scenario without HGT edges if and only if $G$ is a properly colored cograph and $\mathscr{R}$ is consistent; this is decidable in $O(|L|^3 + |L||\mathscr{R}|)$ time.

**Theorem (EDT recognition).** Deciding whether a vertex-colored graph is an EDT graph (EDT-Recognition) is NP-complete, and it remains NP-complete when the input graph is a cograph.

**Corollary (quasi-orthology).** For every generic scenario the EDT graph equals the graph of strict quasi-orthologs, and it is a cograph whenever the scenario is HGT-free or both trees are binary.

## Expansion

In the PDT case the relation is a pure "genes diverged before their species did" comparison, which is monotone along the gene tree and therefore induced by a cotree; same-species genes always diverge before the (leaf) species lca, so they are adjacent in $G$, i.e. non-adjacent pairs have different colors. The triple condition records the species clusterings forced by induced paths. For EDT graphs the equality constraint couples gene-tree and species-tree times exactly; without transfers this collapses to the cograph-plus-consistency test, but with transfers the hardness comes from a reduction from a constrained triple satisfiability problem, itself shown NP-complete via 3-Set Splitting.

## Sources

- David Schaller, Tom Hartmann, Manuel Lafond, Nicolas Wieseke, Peter F. Stadler and Marc Hellmuth, "Relative timing information and orthology in evolutionary scenarios", Algorithms for Molecular Biology 18 (2023), 16, <https://doi.org/10.1186/s13015-023-00240-4>; numbering as in arXiv:2212.02201: Theorems 14–17 (Sections 7–8), Theorem 23 and Corollary 11 (Section 9).
