# Kong–Cox allele-sharing LOD scores

Kong and Cox (1997) start from an allele-sharing test statistic for linkage and propose an associated one-parameter model which, under general missing-data patterns, allows exact calculation of likelihood ratios and LOD scores and hence accurate linkage tests; they also suggest an alternative model that requires additional computation. Under the no-linkage hypothesis the parameter, written $\delta$, is $0$, and larger $\delta$ means more allele sharing among affected relatives (Margaritte-Jeannin et al. 2007, who use the exponential form).

A linear one-parameter family shows why the likelihood ratios are exact. Let $Z$ be an allele-sharing score on the inheritance vectors $v$ of a pedigree, normalized to have mean $0$ and variance $1$ under the no-linkage law $P_0$ of $v$, and set $P_\delta(v) = P_0(v)(1 + \delta Z(v))$. This is a probability law exactly when $1 + \delta Z \ge 0$ on the support, that is for $\delta \in [-1/\max Z, -1/\min Z]$. With marker data $x$, the likelihood is

$$L(\delta) = \sum_v P(x \mid v) P_\delta(v) = L(0)\,\bigl(1 + \delta\, E_0[Z \mid x]\bigr),$$

so the likelihood ratio against $\delta = 0$ is the explicit function $1 + \delta E_0[Z \mid x]$ of the conditional expected score, whatever the pattern of missing marker information, and its derivative at $\delta = 0$ is $E_0[Z \mid x]$.

## Expansion

1. The model: inheritance vectors, the no-linkage law, and normalized sharing scores.
2. Validity of the linear family on the stated interval, and the linear form of the likelihood.
3. The LOD score $\log_{10}(1 + \hat\delta\, E_0[Z \mid x])$ for one pedigree and its sum over independent pedigrees.
4. The exponential family $P_\delta(v) \propto P_0(v) e^{\delta Z(v)}$, its normalizing constant, and its behaviour when the linear family's interval is too narrow.
5. The score test at $\delta = 0$ and its relation to the normalized nonparametric linkage statistic.

## Sources

- A. Kong and N. J. Cox, Allele-sharing models: LOD scores and accurate linkage tests, Am. J. Hum. Genet. 61 (1997), 1179–1188, abstract. <https://doi.org/10.1086/301592>
- P. Margaritte-Jeannin, M.-C. Babron and F. Clerget-Darpoux, On the choice of linkage statistics, BMC Proc. 1, Suppl. 1 (2007), S102, Methods. <https://doi.org/10.1186/1753-6561-1-s1-s102>
