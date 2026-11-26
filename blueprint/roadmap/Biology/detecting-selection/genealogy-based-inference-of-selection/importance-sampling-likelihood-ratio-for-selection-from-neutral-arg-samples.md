# Importance-sampling likelihood ratio for selection from neutral ARG samples

Let $D$ be haplotype data over a region, $G$ its (time-discretized) ancestral recombination graph, and $s$ the selection coefficient at a focal site $k$, all other sites neutral. Assume the data are conditionally independent of $s$ given the full graph, $P(D \mid G, s) = P(D \mid G)$, and let $q(G) = P(G \mid D, s = 0)$ be the posterior of the graph under neutrality, which is positive wherever $P(G, D \mid s) > 0$.

**Identity.** The likelihood ratio against neutrality is an expectation under the neutral posterior:

$$\frac{L(s)}{L(0)} = E_{G \mid D, s=0}\Bigl[\frac{P(G \mid s)}{P(G \mid s = 0)}\Bigr].$$

**Approximation.** Write $G = (G_k, G_{\setminus k})$ with $G_k$ the local tree at the focal site. If $P(G_{\setminus k} \mid G_k, s) \approx P(G_{\setminus k} \mid G_k, s')$ for all $s, s'$, and the local-tree probability depends on $G_k$ only through the allelic-class lineage counts $C_k$ of [the structured-coalescent model](structured-coalescent-hmm-for-a-local-tree-under-selection.md), then for graphs $G^{(1)}, \dots, G^{(M)}$ drawn from the neutral posterior,

$$\widehat{\mathrm{LR}}(s) = \frac1M\sum_{m=1}^M \Omega^{(m)}(s), \qquad \Omega^{(m)}(s) = \frac{P(C_k^{(m)} \mid s)}{P(C_k^{(m)} \mid s = 0)},$$

converges almost surely (by the ergodic theorem for the sampler) to an approximation of $L(s)/L(0)$. The maximum-likelihood estimate is $\hat s = \arg\max_s \widehat{\mathrm{LR}}(s)$, and the posterior marginal of the allele frequency in epoch $i$ is estimated by the self-normalized average

$$\hat\pi(x_i \mid D, s) = \frac{\sum_m P(X_i = x_i \mid C_k^{(m)}, s)\,\Omega^{(m)}(s)}{\sum_m \Omega^{(m)}(s)} .$$

## Proof sketch

For the identity, $E_{G\mid D,0}[P(D,G\mid s)/P(D,G\mid 0)] = \sum_G P(D, G \mid s)/P(D \mid 0) = L(s)/L(0)$, and the conditional independence of $D$ and $s$ given $G$ cancels $P(D \mid G)$ from the ratio. The ratio form is far more stable than estimating $L(s)$ itself, and one set of neutral posterior samples serves every value of $s$ (and richer selection models, such as an onset time), so the expensive graph sampling is done once. The approximation discards the information that selection leaves in the rest of the graph beyond the local tree; the weights $\Omega^{(m)}$ are ratios of the hidden-Markov likelihoods computed with and without selection.

## Depends on

- [Structured-coalescent hidden Markov model for a local tree under selection](structured-coalescent-hmm-for-a-local-tree-under-selection.md)

## Sources

- A. J. Stern, P. R. Wilton and R. Nielsen, "An approximate full-likelihood method for inferring selection and allele frequency trajectories from DNA sequence data", PLoS Genetics 15 (2019), e1008384, "Importance sampling to estimate the likelihood function", Equations (11)–(22), <https://doi.org/10.1371/journal.pgen.1008384> (PMCID: PMC6760815).
