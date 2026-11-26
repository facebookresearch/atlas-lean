# Inconsistency of topology-based summary methods with short loci

Under the MSC+CFN model (gene trees from the multispecies coalescent, $L$ binary sites per locus under the CFN model), a *summary method* estimates the species tree from one estimated gene tree per locus. A summary method $\mathcal{A}$ is *reasonable* if on four-taxon inputs it returns the most frequent quartet topology among the input gene trees (ties broken uniformly at random). In weighted statistical binning (WSB), loci are grouped into bins of mutually compatible gene trees, where two gene trees are incompatible if they have conflicting edges each with bootstrap support above a threshold $B$; a supergene tree is computed by fully partitioned maximum likelihood on each bin and replicated by the bin size before summarization.

**Theorem.**

1. For every locus length $L \in \mathbb{N}$ there is a species tree (topology, branch lengths and mutation rates) such that any reasonable summary method applied to maximum likelihood gene trees is positively misleading: as the number of loci $m \to \infty$ its output topology is unique and differs from the true species tree with probability tending to $1$.
2. With a single site per locus, the WSB pipeline followed by a reasonable summary method is not statistically consistent.
3. For every $L$ there are $B < 1$ and a species tree such that the WSB* pipeline (binning variant) with support threshold $B$ followed by a reasonable summary method is positively misleading.

## Expansion

On short loci the maximum likelihood gene tree of a four-taxon locus in the Felsenstein zone is the long-branch-attraction quartet more often than the true one, so its frequency dominates among the gene trees and any method returning the dominant quartet fails. Binning does not repair this: the newly computed supergene trees have the same distribution as maximum likelihood trees on the original saturated genes, so the bias is preserved. This mirrors the [partitioned likelihood failure](inconsistency-of-fully-partitioned-maximum-likelihood-under-the-multispecies-coalescent.md), and shows that consistency of summary methods under the coalescent requires gene-tree estimation error to vanish.

## Sources

- Sebastien Roch, Michael Nute and Tandy Warnow, *Long-branch attraction in species tree estimation: inconsistency of partitioned likelihood and topology-based summary methods*, arXiv:1803.02800, Theorems 2, 3, 4 and 5 and Corollary 1. <https://doi.org/10.48550/arXiv.1803.02800> Published version: Systematic Biology 68 (2018) 281–297, <https://doi.org/10.1093/sysbio/syy061>.
