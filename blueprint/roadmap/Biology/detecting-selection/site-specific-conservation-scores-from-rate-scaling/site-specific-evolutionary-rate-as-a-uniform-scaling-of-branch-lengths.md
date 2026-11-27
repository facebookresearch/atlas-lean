# Site-specific evolutionary rate as a uniform scaling of branch lengths

**Setting.** Let $\Psi$ be a rooted phylogeny with branch lengths in substitutions per site, and let an alignment column $i$ assign to each leaf $n$ a state $c(i, n) = (s(i-1,n), s(i,n), s(i+1,n))$, where each $s$ is a nucleotide or a gap-size class. Let $p(a, b, t) = \mathrm{subst}(a, b, t) \cdot \mathrm{indel}(a, b, t)$ be the probability of going from state $a$ to state $b$ along a branch of length $t$ under the [context-dependent rate matrix](context-dependent-trinucleotide-substitution-rates-from-a-close-outgroup.md) and the gap model, and let $p'(a, b, t)$ be its version conditioned on the flanking positions, which are held at their most parsimonious labeling so that only the middle base varies.

**Statement** (Asthana et al. 2007, Methods "Computation of evolutionary rate", "Computation of p-value"). Introduce a single rate parameter $\omega > 0$ acting as a uniform scaling of the whole tree, so that a branch of length $t$ contributes $p'(a, b, \omega t)$; a site with $\omega < 1$ evolves more slowly than the neutral expectation and a site with $\omega > 1$ faster. Let $L(\omega)$ be the likelihood of the observed column computed by the standard post-order recursion over $\Psi$ with these scaled transition probabilities and root distribution $\pi$. The site's rate is estimated either by maximizing $L(\omega)$, or, when the mutation rate or the tree depth at that site makes the maximum-likelihood estimate noisy, by the median of the posterior of $\omega$ under a prior on $[0, 1]$ (uniform in the reported analysis); this estimate is the site's conservation score. Its $p$-value, whose exact computation would require summing over all leaf-state combinations, is obtained by Monte Carlo simulation of columns under $\omega = 1$.

## Depends on

- [Context-dependent trinucleotide substitution rates from a close outgroup](context-dependent-trinucleotide-substitution-rates-from-a-close-outgroup.md)
- [The site likelihood by pruning](../../phylogenetics/felsenstein-s-pruning-algorithm/likelihood-eq-sum-prune.md)

## Remarks

Scaling the entire tree by one factor, rather than fitting a rate per branch, keeps a single parameter per site, which is what makes nucleotide-resolution scoring possible; it is the same device as the rate multiplier of discrete rate-heterogeneity models, but estimated per site rather than integrated over. Importantly $\omega$ is defined relative to the neutral tree estimated with the site's own context, so it is independent of the local mutation rate: a CpG position and a non-CpG position with equal $\omega$ are equally constrained even though their absolute substitution rates differ severalfold. Conditioning on the flanking positions keeps the state space at four values per internal node instead of $64$, at the cost of fixing the neighbours by parsimony. The Bayesian estimate with a prior supported on $[0, 1]$ is conservative: it shrinks poorly determined sites towards the slow end only as far as the data support, rather than reporting the extreme maximum-likelihood values that short alignments can produce.

## Sources

- S. Asthana, M. Roytberg, J. Stamatoyannopoulos and S. Sunyaev, "Analysis of sequence conservation at nucleotide resolution", PLoS Computational Biology 3 (2007), e254, Methods ("Computation of evolutionary rate", "Computation of p-value"), <https://doi.org/10.1371/journal.pcbi.0030254>, PMCID PMC2230682.
