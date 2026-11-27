# Consistency of Type 1 tuple methods under full subset coverage

**Setting.** A species tree $\mathcal{T}=(T,\Theta)$ on a taxon set $X$ (topology $T$, branch lengths $\Theta$ in coalescent units, every internal branch of positive length, each taxon labelling exactly one leaf) generates i.i.d. gene trees under the multispecies coalescent (MSC). For gene $i$ and taxon $j$ let $Y_{ij}\in\{0,1\}$ indicate that taxon $j$ is present in the data for gene $i$; the observed gene tree is the true gene tree restricted to the present taxa.
- **$M_{\mathrm{iid}}(p)$:** the $Y_{ij}$ are i.i.d. Bernoulli$(p)$, $0<p<1$, independent of the gene trees.
- **$M_{\mathrm{fsc}}(k)$ (full subset coverage):** deletion is i.i.d. across genes and independent of the gene trees, and every set $B$ of at most $k$ taxa satisfies $\Pr[B\subseteq\text{taxa of a random gene}]=p_B>0$. $M_{\mathrm{iid}}$ is a special case.

**Tuple methods.** An $\ell$-tuple method $A=(F,\alpha)$ computes, from the input $I$ of gene trees, a summary statistic $F_t(I)$ for every tree $t$ on every set $B$ of $\ell$ taxa, then maps the vector $F(I)$ to a species tree $\alpha(F(I))$. It is *Type 1* if $F_q(I)=F_q(I|_B)$ for every input $I$, every $\ell$-set $B$ and every tree $q$ on $B$, i.e. deleting taxa outside $B$ never changes the statistics on $B$. Its *natural extension* to data with missing taxa computes the statistics for $B$ from exactly the genes containing all of $B$ (Definition 1).

**Theorem 4.** Let $A$ be a Type 1 $\ell$-tuple method such that, with no missing data, (i) $F(I_m)\to F_0$ in probability as the number $m$ of genes grows, for a constant vector $F_0$ determined by $\mathcal{T}$, and (ii) there is $\delta>0$ with $\alpha(F_1)=\alpha(F_0)=T$ whenever $\|F_1-F_0\|_\infty<\delta$. If $|X|\ge\ell$, the natural extension of $A$ is statistically consistent under the MSC with $M_{\mathrm{fsc}}(k)$ deletion for every $k\ge\ell$, and hence under every $M_{\mathrm{iid}}(p)$.

**Corollary 5.** ASTRAL, METAL, MP-EST and STEM, run in exact mode, remain statistically consistent under the MSC with $M_{\mathrm{fsc}}(k)$ taxon deletion, for every $k$ at least the size $\ell$ of the taxon tuples on which the method computes its statistics, whenever they are consistent without missing data.

## Depends on

- [Species tree](../species-tree.md)
- [The multispecies coalescent](../gene-tree-prob.md)

## Proof depends on

- [Topology-dependent taxon deletion destroys identifiability](topology-dependent-taxon-deletion-destroys-identifiability.md)

## Expansion

By Lemma 2 of the source, genes containing all of an $\ell$-set $B$ carry, restricted to $B$, exactly the MSC law on $\mathcal{T}|B$, and Type 1 statistics computed from them estimate the same limit $F_0$ as with complete data. Under $M_{\mathrm{fsc}}(k)$ with $k\ge\ell$ each such gene appears with probability $p_B>0$ independently, so by Borel–Cantelli infinitely many genes contain $B$ and each coordinate of the natural extension converges to its coordinate of $F_0$. With finitely many coordinates, eventually $\|F-F_0\|_\infty<\delta$ with probability tending to one, and (ii) returns $T$. Among Type 2 methods that average pairwise distances across gene trees, NJst and ASTRID are not statistically consistent under $M_{\mathrm{iid}}$ (Nute et al., Correction, BMC Genomics 21 (2020) 133, <https://doi.org/10.1186/s12864-020-6540-1>), whereas whether STAR is statistically consistent under $M_{\mathrm{iid}}$ remains an open question (Nute et al. 2018).

## Sources

- M. Nute, J. Chou, E. K. Molloy, T. Warnow, "The performance of coalescent-based species tree estimation methods under models of missing data", BMC Genomics (2018). <https://doi.org/10.1186/s12864-018-4619-8>, PMCID PMC5998899. Definition 1, Theorem 4 and Corollary 5.
