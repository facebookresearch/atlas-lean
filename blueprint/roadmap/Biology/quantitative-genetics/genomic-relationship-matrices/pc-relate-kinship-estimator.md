# PC-Relate kinship estimator under population structure

Let $g_{is} \in \{0,1,2\}$ be the genotype of individual $i$ at SNP $s$, $s = 1,\dots,S$. In a structured or admixed sample, allele frequencies vary between individuals; let $\mu_{is} \in (0,1)$ be the individual-specific allele frequency, so $E[g_{is}] = 2\mu_{is}$. PC-Relate estimates $\mu_{is}$ by regressing the genotypes at SNP $s$ on the top principal components $V_{i1},\dots,V_{iK}$ of ancestry,

$$2\hat\mu_{is} = \hat\beta_{0s} + \sum_{k=1}^K\hat\beta_{ks}V_{ik},$$

with fitted values kept inside $(0,1)$, and estimates the kinship coefficient of individuals $i \ne j$ by

$$\hat\phi_{ij} = \frac{\sum_{s=1}^S (g_{is} - 2\hat\mu_{is})(g_{js} - 2\hat\mu_{js})}{4\sum_{s=1}^S\sqrt{\hat\mu_{is}(1-\hat\mu_{is})\,\hat\mu_{js}(1-\hat\mu_{js})}}.$$

The estimator is the ratio of the summed ancestry-adjusted genotype covariances to their summed scale, under the moment model $E[(g_{is} - 2\mu_{is})(g_{js} - 2\mu_{js})] = 4\phi_{ij}\sqrt{\mu_{is}(1-\mu_{is})\mu_{js}(1-\mu_{js})}$, which reduces to the usual $\operatorname{Cov}(g_{is}, g_{js}) = 4\phi_{ij}\,p_s(1-p_s)$ when all individuals share the frequency $p_s$. The principal components are computed in a way that is robust to the relatives in the sample, so that ancestry and recent relatedness are not confounded.

## Remarks

In a homogeneous population, $\operatorname{Cov}(g_{is}, g_{js}) = 4\phi_{ij}p_s(1-p_s)$ because each of the four allele pairs between $i$ and $j$ is identical by descent with probability $\phi_{ij}$, and the standard method-of-moments estimator divides centred cross-products by $4p_s(1-p_s)$. Under structure, centring at a common frequency inflates cross-products between individuals of similar ancestry, which conventional estimators read as relatedness. Centring each genotype at its own ancestry-predicted mean removes the ancestry component, leaving the covariance due to recent common ancestors; the geometric-mean denominator is the natural scale when the two individuals have different expected frequencies. No ancestral reference populations or explicit admixture model are needed.

## Depends on

- [Kinship coefficient](kinship.md)
- [The genetic relationship covariance](integral-centered-mul.md)

## Sources

- M. P. Conomos, A. P. Reiner, B. S. Weir and T. A. Thornton, "Model-free estimation of recent genetic relatedness", American Journal of Human Genetics (2016), <https://doi.org/10.1016/j.ajhg.2015.11.022> (PMC4716688).
