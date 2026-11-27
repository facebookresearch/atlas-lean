# Depth characterization of anomaly-producing species trees

Consider a rooted binary labelled species tree $\sigma = (\psi, \boldsymbol\lambda)$ with topology $\psi$ on $n$ species and internal branch lengths $\boldsymbol\lambda$ in coalescent units, with one gene lineage sampled per species, evolving under the multispecies coalescent. A labelled gene tree topology $g \ne \psi$ is **anomalous** for $\sigma$ if

$$\mathbb P_\sigma(G = g) > \mathbb P_\sigma(G = \psi).$$

The topology $\psi$ **produces anomalies** if some $\boldsymbol\lambda$ admits an anomalous gene tree. The **depth** of $\psi$ is the maximum, over leaves, of the number of branches on the path from the leaf to the root.

**Theorem.** A labelled species tree topology produces anomalies if and only if its depth is at least $3$; equivalently, if and only if it contains two consecutive internal branches in an ancestor–descendant relationship.

## Depends on

- [Rooted binary species tree with branch lengths](species-tree.md)
- [The multispecies coalescent](gene-tree-prob.md)

## Proof depends on

- [No anomalous gene trees for three species](triple-no-anomaly.md)
- [No anomalous gene trees on the balanced four-species tree](balanced-no-anomaly.md)
- [The four-species anomaly zone](caterpillar-exists-anomalous-iff.md)

## Expansion

Topologies of depth below $3$ are exactly the three-taxon tree and the balanced four-taxon tree, which have no anomalies by direct computation. If the depth is at least $3$, pick consecutive internal branches $e_x$ (ancestral) and $e_y$ with lengths $x, y$, and group the tree into subtrees $A, B$ below $e_y$, $C$ below $e_x$ but not $e_y$, and $D$ the remaining part, so that $\psi$ "caterpillarizes" to the four-taxon caterpillar $(((A,B),C),D)$. Choose $(x, y)$ in the four-taxon anomaly zone, where the balanced topology $L_2 = ((A,B),(C,D))$ has probability exceeding the matching caterpillar, and make every other branch so long that, with joint probability at least $1-\varepsilon$, all lineages in each long branch coalesce on it. Bounding $q_1 = \mathbb P(\text{match}) \le (1-\varepsilon)p_{\mathrm{match}}(x,y) + \varepsilon$ and $q_2 \ge (1-\varepsilon)p_{L_2}(x,y)$, a small enough $\varepsilon$ gives $q_2 > q_1$. The same argument works for any consecutive pair, not only one adjacent to the root. The reformulation shows that anomalies are driven by consecutive short branches (rapid successive speciations on one lineage), not merely by short branches.

## Sources

- N. A. Rosenberg, "Discordance of species trees with their most likely gene trees: a unifying principle", Molecular Biology and Evolution 30(12) (2013) 2709–2713, Eq. 1–2, Theorem 1 and its proof, <https://doi.org/10.1093/molbev/mst160>, PMCID PMC3840310.
