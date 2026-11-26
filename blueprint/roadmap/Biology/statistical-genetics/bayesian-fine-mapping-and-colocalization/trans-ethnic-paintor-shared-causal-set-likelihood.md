# Trans-ethnic fine-mapping with a shared causal set and a logistic annotation prior

For populations $p = 1, \dots, P$ and a locus of $M$ SNPs, let $Z_p \in \mathbb{R}^M$ be the marginal association Z-scores, $\Sigma_p$ the population-specific LD (Pearson correlation) matrix, assumed positive definite, and $\lambda_p \in \mathbb{R}^M$ the non-centrality parameters (NCPs) of the SNPs if causal, $\lambda_{pj} = \beta_{pj}\sqrt{\operatorname{Var}(G_{pj}) N_p}/\sigma_e$. Let $C \in \{0,1\}^M$ indicate the causal SNPs and $A_j$ a vector of functional annotations of SNP $j$.

**Model.**

$$Z_p \mid \lambda_p, C \sim N\big(\Sigma_p(\lambda_p \circ C),\ \Sigma_p\big), \qquad P(C; \gamma) = \prod_{j=1}^{M} \sigma(\gamma^\top A_j)^{C_j}\,\big(1 - \sigma(\gamma^\top A_j)\big)^{1-C_j},$$

with $\sigma(u) = 1/(1 + e^{-u})$ and $\circ$ the entrywise product. The causal set $C$ is shared by all populations while the NCPs may differ. Independent loci $l$ give the likelihood

$$L(\gamma) = \prod_{l} \sum_{C_l} \Big(\prod_{p=1}^{P} \phi\big(Z_{l,p};\ \Sigma_{l,p}(\lambda_{l,p} \circ C_l),\ \Sigma_{l,p}\big)\Big) P(C_l; \gamma),$$

where $\phi(\cdot\,; m, S)$ is the multivariate normal density.

**Posterior.** By Bayes' theorem the posterior of a causal configuration is proportional to $\prod_p \phi(Z_{l,p}; \cdot) P(C_l; \gamma)$, and the posterior probability that SNP $j$ is causal is the sum of these posteriors over configurations with $C_{lj} = 1$.

## Depends on

- [Posterior inclusion probability](pip.md)
## Expansion

The mean $\Sigma_p(\lambda_p \circ C)$ is the LD-induced NCP: a tag SNP $j$ inherits $\sum_c r_{p,jc}\lambda_{pc}$ from the causal SNPs $c$. Because allele frequencies and LD differ between populations, the same causal configuration produces different Z-score patterns, so the product over populations sharpens the posterior where LD in one population breaks a correlation present in another. The annotation effects $\gamma$ are log-odds of causality and are fitted across loci by expectation–maximization, while the NCPs are approximated from the observed Z-scores. In practice $\Sigma_p$ is regularized to be positive definite, the Z-scores are whitened by the inverse Cholesky factor, and the number of causal SNPs per locus is capped at two or three so the sum over configurations is tractable.

## Sources

- G. Kichaev and B. Pasaniuc, "Leveraging Functional-Annotation Data in Trans-ethnic Fine-Mapping Studies", American Journal of Human Genetics 97 (2015), 260–271, Material and Methods, Equations 1–11, <https://doi.org/10.1016/j.ajhg.2015.06.007> (PMC4573268).
