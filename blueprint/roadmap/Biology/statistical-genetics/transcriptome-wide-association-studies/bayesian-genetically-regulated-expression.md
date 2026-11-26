# Bayesian genetically regulated expression with cis- and trans-eQTL spike-and-slab priors

Let $E_g \in \mathbb{R}^n$ be the centered, covariate-adjusted expression of a target gene $g$ in a reference sample, and let the centered genotypes be split into cis-SNPs $X_{\mathrm{cis}}$ (within 1 Mb of the gene) and trans-SNPs $X_{\mathrm{trans}}$ (elsewhere in the genome). The **Bayesian variable selection regression (BVSR) expression model** of BGW-TWAS is

$$E_g = X_{\mathrm{cis}}\, w_{\mathrm{cis}} + X_{\mathrm{trans}}\, w_{\mathrm{trans}} + \epsilon, \qquad \epsilon_i \overset{\mathrm{iid}}{\sim} \mathcal{N}(0, \sigma_\epsilon^2),$$

with independent spike-and-slab priors whose slab variances and inclusion probabilities differ between the two classes:

$$w_{\mathrm{cis},i} \sim \pi_{\mathrm{cis}}\, \mathcal{N}(0, \sigma_{\mathrm{cis}}^2 \sigma_\epsilon^2) + (1 - \pi_{\mathrm{cis}})\, \delta_0, \qquad w_{\mathrm{trans},i} \sim \pi_{\mathrm{trans}}\, \mathcal{N}(0, \sigma_{\mathrm{trans}}^2 \sigma_\epsilon^2) + (1 - \pi_{\mathrm{trans}})\, \delta_0,$$

and conjugate hyperpriors $\pi_{\mathrm{cis}} \sim \mathrm{Beta}(a_{\mathrm{cis}}, b_{\mathrm{cis}})$, $\pi_{\mathrm{trans}} \sim \mathrm{Beta}(a_{\mathrm{trans}}, b_{\mathrm{trans}})$, $\sigma_{\mathrm{cis}}^2 \sim \mathrm{IG}(k_1, k_2)$, $\sigma_{\mathrm{trans}}^2 \sim \mathrm{IG}(k_3, k_4)$. Writing $w_i = \gamma_i \beta_i$ with latent inclusion indicator $\gamma_i \in \{0, 1\}$, the posterior inclusion probability of SNP $i$ is $\mathrm{PP}_i = \mathbb{E}[\gamma_i \mid E_g, X]$.

**Definition (Bayesian GReX).** For test-cohort genotypes $\tilde X$ (columns $\tilde X_i$), the imputed genetically regulated expression is

$$\widehat{\mathrm{GReX}} = \sum_{i=1}^{p} \tilde X_i\, \widehat{\mathrm{PP}}_i\, \hat w_i,$$

where $\hat w_i$ is the posterior mean of $\beta_i$ given inclusion and $\widehat{\mathrm{PP}}_i$ the estimated inclusion probability. Since $\mathbb{E}[w_i \mid \text{data}] = \mathrm{PP}_i\, \mathbb{E}[\beta_i \mid \gamma_i = 1, \text{data}]$, this is the posterior mean of the linear predictor $\tilde X w$, so it averages over uncertainty in which SNPs are eQTL. A transcriptome-wide association study (TWAS) then tests association between $\widehat{\mathrm{GReX}}$ and the phenotype.

## Expansion

The two-class prior lets trans-SNPs, which are far more numerous but individually less likely to be eQTL, receive their own sparsity level $\pi_{\mathrm{trans}}$ and effect-size scale, instead of either excluding them (cis-only methods) or treating them like cis-SNPs. The point mass at zero makes the posterior a mixture over $2^p$ inclusion patterns; the posterior mean of $w_i$ factors into the inclusion probability times the conditional slab mean, which is exactly the weight used in $\widehat{\mathrm{GReX}}$. In practice the posterior is approximated by an expectation-maximization Markov chain Monte Carlo algorithm run on summary statistics (LD and single-variant score statistics) within approximately independent genome blocks.

## Sources

- J. M. Luningham, J. Chen, S. Tang, et al., "Bayesian Genome-wide TWAS Method to Leverage both cis- and trans-eQTL Information through Summary Statistics", American Journal of Human Genetics 107 (2020), 714–726, Material and Methods, Equations 1–5, <https://doi.org/10.1016/j.ajhg.2020.08.022> (PMC7536614).
