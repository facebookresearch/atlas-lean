# Minimum Robinson–Foulds correction for orthology constraints

**Setting.** Let $G$ be a rooted binary gene tree reconciled with a species tree $S$ by the LCA mapping $s(\cdot)$; each internal node is a speciation or a duplication. For trees on the same leaves, $\mathrm{RF}(G,G') = 2c(G,G')$, where $c(G,G')$ is the number of clades of $G$ absent from $G'$. Let $P$ be a symmetric set of gene pairs $(g_1,g_2)$ with $s(g_1) \ne s(g_2)$ that are required to be orthologous; $G$ satisfies $P$ if $\mathrm{lca}_G(g_1,g_2)$ is a speciation for every pair. A pair in $P$ whose LCA in $G$ is a duplication is a false paralogous pair; $P_f$ is the set of these.

**Gene Orthology Correction (GOC).** Find $G_P$ satisfying $P$ with $\mathrm{RF}(G,G_P)$ minimum.

**Non-preservable clades.** For leaves $a,b$ put $r_{a,b} = \mathrm{lca}_G(a,b)$, $s_{a,b} = \mathrm{lca}_S(s(a),s(b))$, and let $h_{a,b}$ be the highest node on the path from $a$ to $r_{a,b}$ (excluding $r_{a,b}$) with $s(h_{a,b})$ a descendant of $s_{a,b}$. Let $H_{a,b}$ be the set of proper ancestors of $h_{a,b}$ that are proper descendants of $r_{a,b}$, and $H = \bigcup_{(a,b)\in P_f} H_{a,b}$.

**Theorem.**
1. If $(a,b)$ is false paralogous and $G'$ makes $a,b$ orthologous, then no clade of a node in $H_{a,b}$ is a clade of $G'$; hence every tree satisfying $P$ misses at least $|H|$ clades of $G$.
2. Every solution of GOC satisfies $\mathrm{RF}(G,G_P) = 2|H|$, and a solution preserving exactly the clades of $V(G)\setminus H$ is constructed in $O(|P|\cdot|V(G)|)$ time by recursively regrafting the subtrees rooted at the highest preservable nodes onto a copy of $S$, so that subtrees with unrelated species images are joined under speciation nodes.
3. (Clade Orthology Correction.) Given a set $C$ of clades of $G$ that are required to be rooted at speciations, a corrected tree exists iff no clade $c \in C$ has $s(c)$ a leaf of $S$, and any two clades of $C$ are either leaf-disjoint or have different species images.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

For a false paralogous pair, a clade above $h_{a,b}$ maps to $s_{a,b}$ or an ancestor and excludes $b$, so in any tree containing it the LCA of $a$ and $b$ would have that clade on one side and $b$ on the other, forcing a duplication; this gives the lower bound. The algorithm attains it: preservable nodes keep their clades because only whole preservable subtrees are moved, required orthologs end up in subtrees whose roots map to the two sides of $s_{g_1,g_2}$ (hence to unrelated species), and grafting each subtree just above its image in a copy of $S$ keeps the skeleton nodes as speciations, so the LCA of any two such subtrees is a speciation.

## Sources

- M. Lafond, M. Semeria, K. M. Swenson, E. Tannier, N. El-Mabrouk, "Gene tree correction guided by orthology", BMC Bioinformatics 14(Suppl 15):S5 (2013), Problems 1–2, Lemma 1, Theorem 1, Definition 1, Lemmas 2–7, Corollary 1 and Theorem 2, <https://doi.org/10.1186/1471-2105-14-S15-S5>, PMCID PMC3851885.
