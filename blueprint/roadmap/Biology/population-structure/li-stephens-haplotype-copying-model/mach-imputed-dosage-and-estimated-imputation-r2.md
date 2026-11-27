# MaCH imputed dosage and the estimated imputation $r^2$

Consider a biallelic SNP with alleles $A$ and $B$ that is imputed by a Markov chain sampler. For one individual, let $n_{A/A}$, $n_{A/B}$, $n_{B/B}$ be the numbers of iterations in which each genotype was sampled, with $I=n_{A/A}+n_{A/B}+n_{B/B}$. Define

- the **genotype score** (imputed dosage of allele $A$) $g=(2n_{A/A}+n_{A/B})/I\in[0,2]$;
- the **most likely genotype** $IG$, the genotype sampled most often, and its **quality score** $Q=n_{IG}/I$.

For a marker with individuals $k=1,\ldots,N$, write $g_k$ for the genotype score of individual $k$ and $m_k=(4n^{(k)}_{A/A}+n^{(k)}_{A/B})/I$ for its sampled second moment (the Monte Carlo estimate of $\mathbb E[G_k^2\mid\text{data}]$). Let $\operatorname{Var}(g)=\frac1N\sum_k g_k^2-\bar g^2$ be the variance of the genotype scores across individuals, with $\bar g=\frac1N\sum_k g_k$, and $\hat p=\bar g/2$ the estimated frequency of $A$. When $0<\hat p<1$, the **estimated $r^2$ with the true genotypes** is

$$\widehat{r^2}=\frac{\operatorname{Var}(g)}{2\hat p(1-\hat p)}.$$

The alternative form replaces the binomial variance by a marker-level estimate of the true genotype variance, built from the individuals' posterior second moments averaged over individuals, minus the square of the average dosage:

$$\widehat{r^2}_{\mathrm{alt}}=\frac{\operatorname{Var}(g)}{\frac1N\sum_{k=1}^N m_k-\bar g^2},$$

defined when this denominator is positive. The denominator is not one individual's conditional variance $m_k-g_k^2$: two perfectly imputed individuals, one $A/A$ and one $B/B$, each have conditional variance $0$, while the marker's genotype variance, and the denominator above, are positive.

**Justification.** Let $G$ be a square-integrable random genotype and $\mathcal F$ a sub-$\sigma$-algebra (the observed data), and put $g=\mathbb E[G\mid\mathcal F]$. Then $\mathbb E[g]=\mathbb E[G]$ and $\operatorname{Cov}(G,g)=\operatorname{Var}(g)$, so whenever $\operatorname{Var}(g)>0$ and $\operatorname{Var}(G)>0$,

$$\operatorname{Corr}(G,g)^2=\frac{\operatorname{Var}(g)}{\operatorname{Var}(G)}\le1.$$

If $G$ is in Hardy–Weinberg proportions with allele frequency $p$, then $\operatorname{Var}(G)=2p(1-p)$ and $\mathbb E[g]=2p$, so $\widehat{r^2}$ is the plug-in estimate of the squared correlation between the imputed dosage and the true allele count when the sampled genotype frequencies are calibrated posterior probabilities.

## Depends on

- [Diploid Li–Stephens model: collapsed forward step and imputed dosage as a posterior mean](diploid-li-stephens-phasing-and-genotype-imputat.md)
- [MaCH mosaic model: per-marker crossover and error parameters, genotype emissions and read-count likelihood](mach-genotype-error-emission-and-read-count-likelihood.md)

## Proof depends on

- [Tower property of conditional expectation](../../../Probability/foundations/conditional-expectation/tower-property/tower-property.md)
- [Total variance splits into true-score and error variance](../../../Probability/statistical-estimation/item-response-models/reliability-and-generalizability/variance-eq-variance-cond-exp-add-varian.md)

## Expansion

- The sampled genotype frequencies $n_{\cdot}/I$ are Monte Carlo estimates of the posterior genotype probabilities, so $g$ estimates the posterior mean dosage.
- $\operatorname{Cov}(G,g)=\mathbb E[(G-\mathbb E G)(g-\mathbb E g)]=\mathbb E[(g-\mathbb E g)^2]$ by the tower property, because $g-\mathbb E g$ is $\mathcal F$-measurable. Dividing $\operatorname{Cov}(G,g)^2=\operatorname{Var}(g)^2$ by $\operatorname{Var}(g)\operatorname{Var}(G)$ gives the ratio; Cauchy–Schwarz gives the bound.
- Perfect information ($g=G$) gives $\widehat{r^2}\approx1$; no information ($g\equiv2p$) gives $\operatorname{Var}(g)=0$. By the law of total variance, $\frac1N\sum_k m_k-\bar g^2$ is the average conditional variance $\frac1N\sum_k(m_k-g_k^2)$ plus $\operatorname{Var}(g)$, so it estimates the marginal genotype variance $\operatorname{Var}(G)$ without assuming Hardy–Weinberg proportions. The paper reports that the first (binomial) denominator performs marginally better than the alternative in practice.

## Sources

- Y. Li, C. J. Willer, J. Ding, P. Scheet, G. R. Abecasis, *MaCH: using sequence and genotype data to estimate haplotypes and unobserved genotypes*, Genetic Epidemiology 34 (2010), 816–834, <https://doi.org/10.1002/gepi.20533>, PMCID PMC3175618 (Appendix: Genotype imputation and estimates of imputation quality).
