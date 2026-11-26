# MaCH imputed dosage and the estimated imputation $r^2$

Consider a biallelic SNP with alleles $A$ and $B$ that is imputed by a Markov chain sampler. For one individual, let $n_{A/A}$, $n_{A/B}$, $n_{B/B}$ be the numbers of iterations in which each genotype was sampled, with $I=n_{A/A}+n_{A/B}+n_{B/B}$. Define

- the **genotype score** (imputed dosage of allele $A$) $g=(2n_{A/A}+n_{A/B})/I\in[0,2]$;
- the **most likely genotype** $IG$, the genotype sampled most often, and its **quality score** $Q=n_{IG}/I$.

For a marker, let $\operatorname{Var}(g)$ be the variance of the genotype scores across individuals and $\hat p=\operatorname{Mean}(g)/2$ the estimated frequency of $A$. The **estimated $r^2$ with the true genotypes** is

$$\widehat{r^2}=\frac{\operatorname{Var}(g)}{2\hat p(1-\hat p)},$$

with the alternative form $\operatorname{Var}(g)\big/\bigl((4n_{A/A}+n_{A/B})/I-[(2n_{A/A}+n_{A/B})/I]^2\bigr)$, which replaces the binomial variance by an empirical second-moment estimate of the genotype variance.

**Justification.** Let $G$ be a square-integrable random genotype and $\mathcal F$ a sub-$\sigma$-algebra (the observed data), and put $g=\mathbb E[G\mid\mathcal F]$. Then $\mathbb E[g]=\mathbb E[G]$ and $\operatorname{Cov}(G,g)=\operatorname{Var}(g)$, so whenever $\operatorname{Var}(g)>0$ and $\operatorname{Var}(G)>0$,

$$\operatorname{Corr}(G,g)^2=\frac{\operatorname{Var}(g)}{\operatorname{Var}(G)}\le1.$$

If $G$ is in Hardy–Weinberg proportions with allele frequency $p$, then $\operatorname{Var}(G)=2p(1-p)$ and $\mathbb E[g]=2p$, so $\widehat{r^2}$ is the plug-in estimate of the squared correlation between the imputed dosage and the true allele count when the sampled genotype frequencies are calibrated posterior probabilities.

## Depends on

- [Diploid Li–Stephens model: collapsed forward step and imputed dosage as a posterior mean](diploid-li-stephens-phasing-and-genotype-imputat.md)
- [MaCH mosaic model: per-marker crossover and error parameters, genotype emissions and read-count likelihood](mach-genotype-error-emission-and-read-count-likelihood.md)

## Expansion

- The sampled genotype frequencies $n_{\cdot}/I$ are Monte Carlo estimates of the posterior genotype probabilities, so $g$ estimates the posterior mean dosage.
- $\operatorname{Cov}(G,g)=\mathbb E[(G-\mathbb E G)(g-\mathbb E g)]=\mathbb E[(g-\mathbb E g)^2]$ by the tower property, because $g-\mathbb E g$ is $\mathcal F$-measurable. Dividing $\operatorname{Cov}(G,g)^2=\operatorname{Var}(g)^2$ by $\operatorname{Var}(g)\operatorname{Var}(G)$ gives the ratio; Cauchy–Schwarz gives the bound.
- Perfect information ($g=G$) gives $\widehat{r^2}\approx1$; no information ($g\equiv2p$) gives $\operatorname{Var}(g)=0$. The paper reports that the first (binomial) denominator performs marginally better than the alternative in practice.

## Sources

- Y. Li, C. J. Willer, J. Ding, P. Scheet, G. R. Abecasis, *MaCH: using sequence and genotype data to estimate haplotypes and unobserved genotypes*, Genetic Epidemiology 34 (2010), 816–834, <https://doi.org/10.1002/gepi.20533>, PMCID PMC3175618 (Appendix: Genotype imputation and estimates of imputation quality).
