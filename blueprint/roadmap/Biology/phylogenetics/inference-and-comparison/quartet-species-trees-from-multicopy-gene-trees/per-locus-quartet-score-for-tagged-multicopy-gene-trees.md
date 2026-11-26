# Per-locus quartet score for tagged multicopy gene trees

Let $\mathcal S$ be a set of $n$ species and let $G$ be a rooted binary gene-family tree whose leaves are mapped to species by $\alpha_G$, with possibly several leaves per species, and whose internal nodes are tagged as speciation or duplication. For a set $Q$ of four leaves, the restriction $G|_Q$ has two degree-three nodes, the anchors of $Q$, and the anchor LCA is their least common ancestor.

- $Q$ is a speciation-driven quartet (SQ) if its four leaves belong to four distinct species and the least common ancestor of every three of its leaves is a speciation node.
- Two SQs are equivalent if they map to the same four species and share the same anchor LCA; equivalent SQs induce the same quartet topology on those species.
- The per-locus quartet score of an unrooted binary species tree $S$ with respect to $G$ is the number of equivalence classes of SQs of $G$ whose induced topology agrees with $S$. A maximum per-locus quartet-score species tree (MLQST) for gene trees $\mathcal G$ maximizes the sum of these scores over $G \in \mathcal G$.

Then:

1. If every gene tree contains only speciation nodes (single-copy), the MLQST problem coincides with the maximum quartet-support species-tree problem; hence it is NP-hard, and its solution is statistically consistent under the multispecies coalescent.
2. Under the gene duplication and loss (GDL) birth–death model, without incomplete lineage sorting, the MLQST is a statistically consistent estimator of the species tree given correctly tagged, error-free gene trees, even when the rooting is only partially correct.
3. Restricted to a search space $X$ of allowed bipartitions, the MLQST is computed by dynamic programming in $O(D\,|X|^{1.73})$ time, where $D$ is the number of distinct speciation-tagged tripartitions in the gene trees; each class is counted once, at its anchor LCA, by tripartition weights summed only over speciation nodes.

## Depends on

- [Consistency of exact quartet-support maximization for the unrooted species tree](../../quartet-support-and-determination-of-trees-by-qu/consistency-of-exact-quartet-support-maximizatio.md)

## Expansion

Under GDL alone, a quartet whose every three-leaf LCA is a speciation node traces orthologous lineages through speciation events, so its topology equals that of the species tree restricted to its four species. Quartets passing through a duplication can disagree with the species tree even without other discordance, and are excluded. Equivalent SQs share their anchoring speciation structure and therefore their topology; counting a whole class once prevents the copy number of a gene family from weighting it. In a single-copy tree every node is a speciation and every quartet is its own class, which gives item 1. The algorithm reuses ASTRAL's recursion $V(A) = \max_{(A', A \setminus A') \in Y}\bigl[V(A') + V(A \setminus A') + W(A' \mid A \setminus A' \mid \mathcal S \setminus A)\bigr]$, changing only the weight $W$. In practice gene trees are rooted and tagged by a parsimony criterion that counts duplications and losses while allowing deep coalescence for free. Disagreements between SQ topologies and the species tree then reflect processes other than GDL, chiefly incomplete lineage sorting, which justifies reusing quartet-frequency branch supports.

## Sources

- C. Zhang, C. Scornavacca, E. K. Molloy, S. Mirarab, "ASTRAL-Pro: quartet-based species-tree inference despite paralogy", *Molecular Biology and Evolution* 37(11) (2020) 3292–3307, Results ("Per-Locus Quartet Similarity", "Statistical Consistency and Local Support") and Materials and Methods ("Notations and Definitions", "Solving the MLQST Problem", Claims 2–3, "Statistical Consistency"), <https://doi.org/10.1093/molbev/msaa139> (PMC7751180).
