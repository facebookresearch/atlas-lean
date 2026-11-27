# Topology-dependent taxon deletion destroys identifiability

**Setting.** A species tree $\mathcal{T}=(T,\Theta)$ on a taxon set $X$ (topology $T$, branch lengths $\Theta$ in coalescent units, every internal branch of positive length, each taxon labelling exactly one leaf) generates i.i.d. gene trees under the multispecies coalescent (MSC). For gene $i$ and taxon $j$ let $Y_{ij}\in\{0,1\}$ indicate that taxon $j$ is present in the data for gene $i$; the observed gene tree is the true gene tree restricted to the present taxa.
- **$M_{\mathrm{iid}}(p)$:** the $Y_{ij}$ are i.i.d. Bernoulli$(p)$, $0<p<1$, independent of the gene trees.
- **$M_{\mathrm{fsc}}(k)$ (full subset coverage):** deletion is i.i.d. across genes and independent of the gene trees, and every set $B$ of at most $k$ taxa satisfies $\Pr[B\subseteq\text{taxa of a random gene}]=p_B>0$. $M_{\mathrm{iid}}$ is a special case.

**Lemma 2 (independent deletion commutes with the coalescent).** If the gene tree and the deletion pattern $Y_i$ of gene $i$ are independent, the observed gene tree has the MSC distribution on the restricted species tree $\mathcal{T}|Y_i$, whichever is generated first.

**Theorem 3.** If $|X| \ge 4$ and taxon deletion may depend on the gene tree topology, there is a dependency structure under which no species tree estimator is statistically consistent.

## Depends on

- [Species tree](../species-tree.md)
- [The multispecies coalescent](../gene-tree-prob.md)

## Expansion

Lemma 2 follows from the memoryless property of coalescence: pruning absent lineages does not change the coalescence law of the remaining lineages inside $\mathcal{T}|Y_i$. For Theorem 3, take two species trees $T\ne T'$ with different unrooted topologies, which exist because $|X| \ge 4$ (with at most three taxa there is only one unrooted topology, and a constant estimator is consistent). Under the MSC on either one, every unrooted gene tree topology, in particular $T'$, has positive probability. Let gene $i$ keep all taxa if its gene tree has topology $T'$ and lose all taxa otherwise. The observed data then consist only of gene trees of topology $T'$, whether the model tree is $T$ or $T'$, so the model species tree is not identifiable from the data distribution.

## Sources

- M. Nute, J. Chou, E. K. Molloy, T. Warnow, "The performance of coalescent-based species tree estimation methods under models of missing data", BMC Genomics (2018). <https://doi.org/10.1186/s12864-018-4619-8>, PMCID PMC5998899. Section "Theoretical framework", Lemma 2 and Theorem 3.
