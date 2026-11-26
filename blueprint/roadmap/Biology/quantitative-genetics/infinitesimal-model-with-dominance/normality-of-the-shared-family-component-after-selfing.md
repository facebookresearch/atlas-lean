# Normality of the shared family component after selfing

In the setting of the infinitesimal model with dominance ($M$ unlinked loci with bounded additive and dominance effects of size $1/\sqrt M$, unrelated founders sampled from an ancestral population in linkage and Hardy–Weinberg equilibrium, bounded scaled inbreeding depression $\iota$), consider a first-generation family whose two parents are the same individual, so $i[1]=i[2]$ (selfing). Let $W=\mathcal A+\mathcal D+E$ be the component of the trait shared by the family: the additive and dominance contributions shared by all offspring plus environmental noise.

Then for every absolutely continuous test function $h$ with $\|h'\|_\infty<\infty$,
$$
\Big|\,\mathbb E\big[h(W)\,\big|\,i[1]=i[2],\ \widetilde Z^{i[1]}\big]-\mathcal N_{\mu_W,\sigma_W^2}(h)\Big|\le\frac{C\,\|h'\|_\infty}{\sqrt M},
$$
where $\mathcal N_{\mu,\sigma^2}(h)$ is the expectation of $h$ under a normal law with that mean and variance, $\mu_W$ is the conditional mean of the shared component given the parent's observed trait, and $\sigma_W^2$ is the environmental variance plus the conditional variance of the shared genetic part. Thus, even after selfing, when additive and dominance effects are correlated through the parent's homozygosity, the shared part is asymptotically Gaussian with mean and variance determined by ancestral quantities and the parent's trait.

## Depends on

- [Asymptotic normality of within-family residuals under dominance](asymptotic-normality-of-within-family-residuals-under-dominance.md)

## Expansion

When the parents coincide, the shared component is no longer a sum of independent locus contributions that are uncorrelated with the conditioning trait, so the dependency-graph Berry–Esseen argument does not apply directly. The proof builds an exchangeable pair $(W,W')$ by resampling one locus and applies Stein's method (Chen–Goldstein–Shao, Proposition 2.4) to bound the smooth-function distance to the normal law by $C\|h'\|/\sqrt M$.

## Sources

- N. H. Barton, A. M. Etheridge and A. Véber, "The infinitesimal model with dominance", arXiv:2211.03515 (2022), Theorem 5.2 and Appendix (Corollary 11.4); published in Genetics (2023). <https://doi.org/10.48550/arXiv.2211.03515>
