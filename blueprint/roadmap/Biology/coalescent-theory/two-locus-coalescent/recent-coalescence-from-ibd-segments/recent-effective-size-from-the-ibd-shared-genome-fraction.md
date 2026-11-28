# Recent effective size from the IBD-shared genome fraction

**Coalescence before a threshold.** In a population of constant effective size $N_e$ (time in generations), the pairwise coalescence time $t$ at a site is exponential with mean $N_e$, so for a threshold $T > 0$

$$P(t \le T \mid N_e) = \int_0^T \frac{1}{N_e}e^{-t/N_e}\,dt = 1 - e^{-T/N_e} \approx \frac{T}{N_e} \quad (N_e \gg T).$$

**Unbiasedness of the shared fraction.** For a pair of haplotypes and a set $\Gamma$ of sites, let $f_T = |\Gamma|^{-1}\sum_{\gamma\in\Gamma}\mathbf 1[t_\gamma < T]$ be the fraction of sites whose coalescence time is below $T$ (in practice, the fraction of the genome covered by IBD segments with TMRCA below $T$). Under any demographic model $\theta$ in which the marginal law of $t_\gamma$ is the same at every site,

$$\mathbb E[f_T \mid \theta] = P(t \le T \mid \theta).$$

**Estimator.** With $\bar f_T$ the mean of $f_T$ over sampled pairs, the aggregate recent effective size over the last $T$ generations is

$$\hat N_e = \frac{T}{\bar f_T}.$$

**Age of a segment from its length.** If the TMRCA of a randomly chosen IBD segment is $g$ generations, its genetic length $l$ (in Morgans) is exponential with rate $2g$, with likelihood $L(g) = 2g\,e^{-2lg}$; since $L'(g) = 2e^{-2lg}(1-2lg)$, the maximum-likelihood age is $\hat g = 1/(2l)$.

## Depends on

- [Holding times of Kingman's coalescent](../../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)

## Expansion

The unbiasedness follows by linearity of expectation over sites. Inverting $P(t \le T) \approx T/N_e$ with the empirical fraction gives $\hat N_e$, a single size averaged over the last $T$ generations rather than a fitted size history. The length law reflects the $2g$ meioses separating the two haplotypes through the common ancestor, each placing crossovers as a Poisson process of rate one per Morgan; coalescent-HMM decoding of the segment (averaging posterior TMRCA estimates along it) gives an alternative age estimate.

## Sources

- J. Nait Saada, G. Kalantzis, D. Shyr, F. Cooper, M. Robinson, A. Gusev, P. F. Palamara, "Identity-by-descent detection across 487,409 British samples reveals fine scale population structure and ultra-rare variant associations", Nature Communications (2020), Methods ("Estimating the age of an IBD segment" and "Effective population size estimate"), <https://doi.org/10.1038/s41467-020-19588-x>.
