# Duplication cost of a minimum isorthology-respecting history

Let $G$ be a gene tree and $S$ a species tree, internal nodes of $G$ labelled speciation or duplication by the LCA mapping. Assume (i) after each duplication exactly one copy retains the parental function, and (ii) $G$ has the isolocalization property and, restricted to any three isorthologous genes from genomes $i,j,k$, agrees with $S$ restricted to $i,j,k$. A **speciation subtree** of $G$ is a subtree whose internal nodes are all speciations.

**Lemma 1.** For isorthologous $a_i, a_j$, the node $\mathrm{lca}_G(a_i,a_j)$ is a speciation.

**Corollary.** Every isorthogroup is the leaf set of a speciation subtree of $G$.

A history $H$ is an **isorthology-respecting history** (IRH) for $(G,S)$ if each isorthogroup induced by $H$ is the leaf set of a speciation subtree of $G$; a **minimum IRH** (MIRH) minimizes a duplication, loss or mutation cost.

**Lemma 2.** A MIRH $H$ has $n$ isorthogroups if and only if it has $n - 1$ duplications.

**Theorem.** If $\mathcal{F}$ is the set of $n$ maximal speciation subtrees of $G$, then a MIRH for $(G,S)$ under the duplication cost has exactly $n-1$ duplications; the cost is computable in linear time.

## Depends on

- [Isolocalization confounds gene tree reconciliation](isolocalization-confounds-gene-tree-reconciliation.md)
- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

Along the path in $H$ between two genes of the same isorthogroup, every duplication is passed through retainer copies (both genes descend from retainers), whereas between genes of different maximal speciation subtrees some duplication is passed through a mutant. Each duplication splits off exactly one new non-isorthologous lineage, so $n$ isorthogroups need $n-1$ duplications and conversely (Lemma 2). Coarser partitions into speciation subtrees can only lower the count, so the maximal speciation subtrees give the minimum. The MIRH discards the gene tree's topology above the isorthologous subtrees; a variant that also respects gene-tree triplets across isorthogroups (minimum triplet-respecting history) keeps more of it.

## Sources

- K. M. Swenson and N. El-Mabrouk, "Gene trees and species trees: irreconcilable differences", BMC Bioinformatics 13 (Suppl 19) (2012), S15, Hypothesis 2, Lemmas 1–4, Corollary 3, Definitions 6–7 and Theorem 2, <https://doi.org/10.1186/1471-2105-13-S19-S15>, PMCID: PMC3526438.
