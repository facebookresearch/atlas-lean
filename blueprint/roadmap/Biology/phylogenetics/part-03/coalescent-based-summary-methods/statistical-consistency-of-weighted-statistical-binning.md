# Statistical consistency of weighted statistical binning

**Setting (GTR+MSC model).** Gene trees $t_1,\dots,t_p$ are sampled from a species tree $T_{sp}$ under the multispecies coalescent; each gene $i$ is equipped with its own GTR parameters $\theta_i$ (branch lengths and a $4\times 4$ substitution matrix), and an alignment $S_i$ of $k$ sites evolves down $T_i = (t_i,\theta_i)$. A *phylogenomic pipeline* is statistically consistent if its species-tree estimate converges in probability to $T_{sp}$ as both $p \to \infty$ and $k \to \infty$. A *coalescent-based summary method* is one that converges in probability to $T_{sp}$ as the number of true gene trees sampled from the multispecies coalescent grows.

**Statistical binning.** Given a bootstrap threshold $B < 1$, genes are placed in bins so that, within each bin, the estimated gene trees have no pairwise conflict on branches with bootstrap support above $B$; each bin is concatenated into a supergene and a supergene tree is estimated by fully partitioned GTR maximum likelihood. *Unweighted* binning passes one supergene tree per bin to the summary method; *weighted* binning replicates each supergene tree as many times as there are genes in its bin.

**Theorem 1 (long sequences make bins pure).** For every $\epsilon < 1$ and $B < 1$ there is a sequence length $L$ such that, if each gene has at least $L$ sites, then with probability at least $1-\epsilon$: every estimated gene tree has the true unrooted topology with all branches supported above $B$; every bin contains genes with the same estimated topology; and all genes with the same true topology share a bin.

**Theorem 2.** The pipeline GTR maximum likelihood gene trees $\to$ weighted statistical binning $\to$ coalescent-based summary method is statistically consistent under the GTR+MSC model.

**Theorem 3.** The same pipeline with unweighted statistical binning is statistically inconsistent under the GTR+MSC model.

## Depends on

- [Multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/README.md)

## Expansion

ML under GTR is consistent, so for long enough alignments each gene tree is correct with high bootstrap support; when all trees have support above $B$, two genes are compatible exactly when their topologies coincide, so bins become topology classes (Theorem 1). A partitioned ML analysis of alignments that share an optimal topology returns that topology, so each supergene tree equals the common true gene tree. Weighted binning then reproduces the multiset of true gene trees exactly, and the summary method's own consistency finishes Theorem 2. Under unweighted binning, as $p \to \infty$ every gene-tree topology (all have positive probability under the multispecies coalescent) eventually forms a bin, so the summary method receives each topology once: a flat distribution from which the species tree cannot be recovered (Theorem 3).

## Sources

- M. S. Bayzid, S. Mirarab, B. Boussau, T. Warnow, "Weighted statistical binning: enabling statistically consistent genome-scale phylogenetic analyses", PLoS ONE 10(6) (2015) e0129183, Definitions 1–3, Lemmas 1–2, Theorems 1–3 and Corollary 1, <https://doi.org/10.1371/journal.pone.0129183>, PMCID PMC4472720.
