# Consistency of NJst and ASTRID under i.i.d. taxon deletion

**Setting.** A species tree $\mathcal{T}=(T,\Theta)$ on a taxon set $X$ (topology $T$, branch lengths $\Theta$ in coalescent units) generates i.i.d. gene trees under the multispecies coalescent (MSC). For gene $i$ and taxon $j$ let $Y_{ij}\in\{0,1\}$ indicate that taxon $j$ is present in the data for gene $i$; the observed gene tree is the true gene tree restricted to the present taxa.
- **$M_{\mathrm{iid}}(p)$:** the $Y_{ij}$ are i.i.d. Bernoulli$(p)$, $0<p<1$, independent of the gene trees.
- **$M_{\mathrm{fsc}}(k)$ (full subset coverage):** deletion is i.i.d. across genes and independent of the gene trees, and every set $B$ of at most $k$ taxa satisfies $\Pr[B\subseteq\text{taxa of a random gene}]=p_B>0$. $M_{\mathrm{iid}}$ is a special case.

**Internode distance methods.** For a gene tree $g$ and taxa $x_i,x_j$ in $g$, let $\rho_g(x_i,x_j)$ be the number of internal nodes on the path between them. NJst and ASTRID average $\rho_g(x_i,x_j)$ over the genes containing both taxa and apply neighbor joining (NJst) or FastME (ASTRID) to the resulting distance matrix. These are Type 2 methods: deleting other taxa from a gene tree changes $\rho_g$.

**Theorem 11.** Under the MSC with $M_{\mathrm{iid}}(p)$ taxon deletion, NJst and ASTRID are statistically consistent.

## Depends on

- [Species tree](../multispecies-coalescent/species-tree.md)
- [Consistency of Type 1 tuple methods under full subset coverage](consistency-of-tuple-methods-under-full-subset-coverage.md)

## Expansion

Neighbor joining returns the topology of an additive matrix whenever every entry is perturbed by less than half its smallest entry, and FastME has a similar error tolerance. By the weak law of large numbers the averaged internode distances converge to their expectations, so it suffices that the expected matrix $\bigl(\mathbb{E}\rho(x_i,x_j)\bigr)$, taken over the MSC gene tree and the $M_{\mathrm{iid}}$ deletion, is additive on $T$, i.e. satisfies the four-point condition on every quartet. Lemma 12 handles the event that four lineages enter a common ancestral population without coalescing: there the expected distance between two of them splits into one term per lineage plus a constant independent of the pair, so the four-point condition holds on that event, which contains every case where the gene quartet disagrees with the species quartet. The concordant case is proved by induction on the number of taxa, starting from $n=4$, where the expected internode distances are computed in closed form and checked directly.

## Sources

- M. Nute, J. Chou, E. K. Molloy, T. Warnow, "The performance of coalescent-based species tree estimation methods under models of missing data", BMC Genomics (2018). <https://doi.org/10.1186/s12864-018-4619-8>, PMCID PMC5998899. Theorem 11 and Lemma 12.
