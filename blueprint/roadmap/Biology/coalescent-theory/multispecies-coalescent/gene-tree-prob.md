# The multispecies coalescent

For a [species tree](species-tree.md) $T$ on the species $\{0, \dots, n-1\}$ and a set $E$ of gene trees, each gene tree given by its set of clusters, the weight $P_T(E)$ is defined as follows:

- for a leaf $\ell(i)$, $P_T(E) = 1$ if the gene tree $\{\{i\}\}$ is in $E$, and $0$ otherwise;
- for a node $(l, r, t)$, $P_T(E)$ is obtained from the [exit laws](exit-law.md) of $l$ and $r$: given $m_l$ lineages $b_l$ and clusters $A_l$ leaving $l$, and $m_r$ lineages $b_r$ and clusters $A_r$ leaving $r$, all $m = m_l + m_r$ lineages coalesce in the root population by random joining, and the contribution is the probability, under the uniform law on ranked histories $h$ of $m$ lineages, that $A_l \cup A_r$ together with the [clusters formed along](clades-along.md) the $m - 1$ events of $h$ started from $b_l$ followed by $b_r$ is a gene tree in $E$.

This is the multispecies coalescent with one lineage sampled per species: below the root each branch population runs Kingman's coalescent for the length of its branch ([branch step](branch-step.md)), and in the root population all remaining lineages coalesce. The definition accepts any real branch lengths. On species trees with [nonnegative branch lengths](nonneg-lengths.md) it is a probability law on gene trees ([nonnegativity](gene-tree-prob-nonneg.md), [additivity](gene-tree-prob-or.md), [normalization](gene-tree-prob-true.md)); otherwise it is only a signed weight: with internal branch length $-1$, the matching three-species gene tree gets $1 - \frac{2}{3} e < 0$.

## Sources

- P. Pamilo and M. Nei, *Relationships between gene trees and species trees*, Mol. Biol. Evol. 5 (1988), 568–583.
- J. H. Degnan and L. A. Salter, *Gene tree distributions under the coalescent process*, Evolution 59 (2005), 24–37.
