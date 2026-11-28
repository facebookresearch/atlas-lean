# Variance of kinship-corrected gene diversity estimators

**Setting.** As in [Unbiased gene diversity estimator from linear allele-frequency estimators](unbiased-gene-diversity-estimator-from-linear-allele-frequency-estimators.md): a locus with allele frequencies $p_1, \dots, p_I$, a sample of $n$ individuals of arbitrary ploidy, relatedness and inbreeding, a linear allele-frequency estimator $\breve p_i = \sum_k w_k X_k(i)$ with weights $0 \le w_k \le 1$ and $\sum_k w_k = 1$ (the source's Eq. 5), and the unbiased estimator $\breve H = (1 - \sum_i \breve p_i^2)/(1 - \rho_2)$. Besides the pairwise kinship $\Phi_{jk}$, let $\Phi_{jkj'}$ be the probability that three alleles drawn one each from $j, k, j'$ are all IBD, $\Phi_{jkj'k'}$ the probability that four alleles drawn one each from $j, k, j', k'$ are all IBD, and $\Phi_{jk,j'k'}$ the joint probability that the alleles from $j$ and $k$ are IBD and the alleles from $j'$ and $k'$ are IBD (individuals not necessarily distinct). Define the weighted mean coefficients

$$\rho_2 = \sum_{j,k} w_j w_k \Phi_{jk}, \quad \rho_3 = \sum_{j,k,j'} w_j w_k w_{j'} \Phi_{jkj'}, \quad \rho_4 = \sum_{j,k,j',k'} w_j w_k w_{j'} w_{k'} \Phi_{jkj'k'}, \quad \rho_{2,2} = \sum_{j,k,j',k'} w_j w_k w_{j'} w_{k'} \Phi_{jk,j'k'} .$$

**Proposition 4.** $\operatorname{Var}[\breve H] = (1 - \rho_2)^{-2}\operatorname{Var}\big[1 - \sum_i \breve p_i^{\,2}\big]$ with

$$\operatorname{Var}\Big[1 - \sum_{i=1}^I \breve p_i^{\,2}\Big] = \rho_{2,2} - \rho_2^2 + 2(\rho_2^2 - \rho_4)\sum_i p_i^2 + 4(2\rho_4 + \rho_2 - 2\rho_3 - \rho_{2,2})\sum_i p_i^3 + (3\rho_{2,2} + 8\rho_3 - 6\rho_4 - 4\rho_2 - \rho_2^2)\Big(\sum_i p_i^2\Big)^2 .$$

**Approximation.** If no sampled individual is related to more than one other, $\rho_3$, $\rho_4$, $\rho_{2,2}$ and $\rho_2^2$ are negligible against $\rho_2$ and

$$\operatorname{Var}\Big[1 - \sum_{i=1}^I \breve p_i^{\,2}\Big] \approx 4\rho_2\Big[\sum_i p_i^3 - \Big(\sum_i p_i^2\Big)^2\Big].$$

The sample-proportion estimator $\tilde H$ and the BLUE-based estimator $\tilde H_{\mathrm{BLUE}}$ are the cases $w_k = m_k/\sum_j m_j$ and $w = K^{-1}\mathbf 1/(\mathbf 1^{\mathsf T}K^{-1}\mathbf 1)$, the latter when its weights lie in $[0,1]$.

## Depends on

- [Unbiased gene diversity estimator from linear allele-frequency estimators](unbiased-gene-diversity-estimator-from-linear-allele-frequency-estimators.md)

## Expansion

The variance requires $\mathbb{E}[\breve p_i^4]$ and $\mathbb{E}[\breve p_i^2 \breve p_{i'}^2]$, i.e. joint probabilities that four allele draws carry given types. Conditioning on the 15 identity-by-descent states of four alleles (Gillois, Cockerham) writes each such probability as a polynomial in $p_i$, $p_{i'}$ whose coefficients are linear in the pair, trio, quartet and pair-of-pairs kinship coefficients; weighting by $w_j w_k w_{j'} w_{k'}$ and summing turns these into $\rho_2, \rho_3, \rho_4, \rho_{2,2}$. The same structure, with two sets of weights, yields an approximate (delta-method) variance for the $F_{ST}$ estimator $(\breve H_{12} - \tfrac12(\breve H_1 + \breve H_2))/\breve H_{12}$, and the smaller variance of the BLUE-based within-population diversities carries over to $F_{ST}$.

## Sources

- A. M. Harris and M. DeGiorgio, "An unbiased estimator of gene diversity with improved variance for samples containing related and inbred individuals of any ploidy", G3: Genes, Genomes, Genetics 7(2) (2017) 671–691, Proposition 4, Eqs. (9)–(11) and Proposition 6, <https://doi.org/10.1534/g3.116.037168>, PMCID PMC5295611.
- M. DeGiorgio, I. Jankovic and N. A. Rosenberg, "Unbiased estimation of gene diversity in samples containing related individuals: exact variance and arbitrary ploidy", Genetics 186 (2010) 1367–1387, Appendix B (the sample-proportion case).
