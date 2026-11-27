# Normality of the shared family component after selfing

In the setting of the infinitesimal model with dominance ($M$ unlinked loci with bounded additive and dominance effects of size $1/\sqrt M$, unrelated founders sampled from an ancestral population in linkage and Hardy–Weinberg equilibrium, bounded scaled inbreeding depression $\iota$), consider a first-generation family whose two parents are the same individual, so $i[1]=i[2]$ (selfing). Observed traits are $\widetilde Z^i=Z^i+E^i$ with environmental noise $E^i\sim N(0,\sigma_E^2)$, $\sigma_E^2>0$, independent of the genetic components and shared by all offspring of a family. Let $W=\mathcal A+\mathcal D+E$ be the component of the trait shared by the family: the additive and dominance contributions shared by all offspring plus the family's shared environmental noise $E$.

Then for every absolutely continuous test function $h$ with $\|h'\|_\infty<\infty$,

$$
\Big|\,\mathbb E\big[h(W)\,\big|\,i[1]=i[2],\ \widetilde Z^{i[1]}\big]-\mathcal N_{\mu_W,\sigma_W^2}(h)\Big|\le\frac{C\,\|h'\|_\infty}{\sqrt M},
$$

where $\mathcal N_{\mu,\sigma^2}(h)$ is the expectation of $h$ under a normal law with that mean and variance, $\mu_W$ is the conditional mean of the shared component given the parent's observed trait, and $\sigma_W^2>0$ is the environmental variance $\sigma_E^2$ plus the conditional variance of the shared genetic part. The constant $C$ depends on $B$ and $\iota$, and is large when the parent's trait is extreme or the offspring trait variance is small. The Gaussian, family-shared noise matters: with merely independent non-Gaussian noise the conclusion fails (for zero genetic effects and two-point noise, $W$ has a two-point law for every $M$). Thus, even after selfing, when additive and dominance effects are correlated through the parent's homozygosity, the shared part is asymptotically Gaussian with mean and variance determined by ancestral quantities and the parent's trait.

## Depends on

- [Asymptotic normality of within-family residuals under dominance](asymptotic-normality-of-within-family-residuals-under-dominance.md)

## Expansion

When the parents coincide, the shared component is no longer a sum of independent locus contributions that are uncorrelated with the conditioning trait, so the dependency-graph Berry–Esseen argument does not apply directly. The proof builds an exchangeable pair $(W,W')$ by resampling one locus and applies Stein's method for exchangeable pairs (Chen–Goldstein–Shao, Proposition 2.4, as Proposition D.3 and Corollary D.4 of the source) to bound the smooth-function distance to the normal law by $C\|h'\|/\sqrt M$.

## Sources

- Nicholas H. Barton, Alison M. Etheridge and Amandine Véber, "The infinitesimal model with dominance", *Genetics* 225 (2023), iyad133, <https://doi.org/10.1093/genetics/iyad133>. Numbering as in the preprint arXiv:2211.03515v3, <https://arxiv.org/abs/2211.03515v3>: Section 5 (the paragraph "Main results" on the Gaussian shared environmental noise), Theorem 5.2 with Remark 5.3, and Appendix D (Proposition D.3 and Corollary D.4).
