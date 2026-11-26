# Genomic SEM factor model and SNP heterogeneity test

**Inputs.** For $k$ traits, multivariable LD-score regression on GWAS summary statistics gives an estimated $k \times k$ genetic covariance matrix $S$ (SNP heritabilities on the diagonal, liability-scale for case–control traits; coheritabilities off the diagonal) together with the sampling covariance matrix $V_S$ of the nonredundant elements $\operatorname{vech}(S)$. The diagonal of $V_S$ carries the squared standard errors, and its off-diagonal elements carry sampling dependencies, which are estimated from the data and absorb sample overlap between GWAS.

**Genome-wide factor model.** A confirmatory factor model with loading matrix $\Lambda$ ($k \times q$), factor covariance $\Phi$ and diagonal residual genetic variances $\Theta$ implies

$$\Sigma(\theta) = \Lambda\,\Phi\,\Lambda^\top + \Theta,$$

and its parameters $\theta$ are estimated by fitting $\Sigma(\theta)$ to $S$ with discrepancies weighted according to $V_S$. Second-order models (a general factor loading on the first-order factors) have the same form with $\Phi$ itself structured. Overfitting is checked by choosing the loading pattern by exploratory factor analysis on one half of the chromosomes and fitting the confirmatory model on the other half.

**Multivariate GWAS.** For each SNP, the vector of its standardized marginal effects on the $k$ traits is appended to the model as an exogenous variable whose path to a latent factor is the SNP's factor effect, tested genome-wide.

**Heterogeneity statistic $Q_{\mathrm{SNP}}$.** Compare the common-pathway model, in which the SNP acts on the indicators only through the factor, with the independent-pathways model, in which the SNP has separate direct paths to the factor's indicators. The difference in model $\chi^2$ is $Q_{\mathrm{SNP}}$, asymptotically $\chi^2$ with degrees of freedom equal to the number of extra paths under the common-pathway null; large values flag SNPs whose effects are not mediated by the factor.

## Expansion

Because $S$ and $V_S$ come from summary statistics alone, traits whose GWAS share participants can be modelled jointly: overlap inflates the cross-trait LD-score intercepts and enters $V_S$, but does not bias the genetic covariances. In 14 psychiatric disorders a correlated five-factor model (compulsive, schizophrenia–bipolar, neurodevelopmental, internalizing and substance-use-disorder factors) fitted with comparative fit index $0.973$ and standardized root mean square residual $0.073$ on the held-out chromosomes, and a second-order general factor was modelled above them.

## Sources

- A. D. Grotzinger, J. Werme, W. J. Peyrot et al., "Mapping the genetic landscape across 14 psychiatric disorders", Nature (2025), Methods ("Genomic SEM": "Genome-wide models" and "Multivariate GWAS"), <https://doi.org/10.1038/s41586-025-09820-3>.
