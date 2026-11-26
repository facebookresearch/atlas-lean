# Joint likelihood mapping (JLIM) statistic for a shared causal variant

Two traits are measured in non-overlapping samples: a primary trait with z-scores $Z = (z_i)$ and a secondary trait with z-scores $W = (w_i)$ at the same $M$ SNPs. Each trait is assumed to have at most one causal variant in the locus. Fix a resolution $\theta \in (0,1)$ (the paper uses $0.8$) and let $N^1_\theta(i)$ and $N^2_\theta(i)$ be the sets of SNPs $j$ with $r^2_{ij} > \theta$ in the LD panels of the two studies. Let $L_1(i)$ and $L_2(i)$ be the likelihoods that SNP $i$ is the causal variant for the primary and secondary trait, and let $m^*$ be the SNP most associated with the primary trait.

**Statistic.**

$$\Lambda = \sum_{i \in N^1_\theta(m^*)} L_1(i)\left(\log L_2(i) - \max_{j \notin N^2_\theta(i)} \log L_2(j)\right),$$

the primary-trait-weighted log-likelihood ratio that the secondary causal variant is the same as, rather than distinct from, the primary one. Using the [profile likelihood of a single causal variant](profile-likelihood-of-a-single-causal-variant.md), $L_1(i) \propto e^{z_i^2/2}$ and $\log L_2(i) - \log L_2(j) = \tfrac12(w_i^2 - w_j^2)$, so up to a positive constant factor

$$\Lambda \;\propto\; \sum_{i \in N^1_\theta(m^*)} e^{\frac12(z_i^2 - z_{m^*}^2)}\left(w_i^2 - \max_{j\notin N^2_\theta(i)} w_j^2\right).$$

**Testing.** The p-value is computed by permuting secondary-trait phenotypes, i.e. under $H_0$: no causal variant for the secondary trait. Under $H_2$: distinct causal variants, the paper shows that, as the non-centrality of the causal variants grows, $P_{\mathrm{JLIM}} = P(\Lambda \ge l \mid H_0) \ge P(\Lambda \ge l \mid H_2)$, so a test calibrated under $H_0$ is asymptotically conservative against $H_2$.

## Remarks

Each summand compares the best secondary-trait fit at a primary candidate $i$ with the best secondary-trait fit anywhere outside the LD neighbourhood of $i$; it is positive when the secondary signal peaks within resolution $\theta$ of $i$ and negative when it peaks elsewhere. Weighting by $L_1(i)$ integrates over uncertainty in the primary causal variant, and normalizing by $L_1(m^*)$ only rescales $\Lambda$. The asymmetric design needs only summary statistics for the primary trait (reference-panel LD) but genotypes for the secondary trait, which makes phenotype permutation possible.

## Depends on

- [Profile likelihood of a single causal variant from association z-scores](profile-likelihood-of-a-single-causal-variant.md)

## Sources

- S. Chun, A. Casparino, N. A. Patsopoulos et al., "Limited statistical evidence for shared genetic effects of eQTLs and autoimmune-disease-associated loci in three major immune-cell types", Nature Genetics (2017), Online Methods, "Joint likelihood mapping (JLIM)", <https://doi.org/10.1038/ng.3795> (PMC5374036).
