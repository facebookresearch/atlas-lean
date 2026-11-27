# The ACE variance-component model for twin and sibling data

**Model.** For individual $j$ in family $i$ write the standardized phenotype, after regressing out measured covariates, as

$$y_{ij} = a\,A_{ij} + c\,C_i + e\,E_{ij},$$

with $A_{ij}$ the additive genetic value, $C_i$ the environment shared by family members, $E_{ij}$ the nonshared environment (measurement error included), all three standard normal, mutually independent, and $C$ constant within a family. Under random mating, no gene–environment correlation or interaction, and the equal-environments assumption (shared environment acts alike on monozygotic and dizygotic pairs),

$$\operatorname{Var} y = a^2 + c^2 + e^2, \qquad \operatorname{Cor}(y_{i1}, y_{i2}) = \begin{cases} a^2 + c^2, & \text{monozygotic pair},\\[2pt] \tfrac12 a^2 + c^2, & \text{dizygotic pair or full siblings}.\end{cases}$$

**Identification.** With the phenotypic variance scaled to one, so $a^2 + c^2 + e^2 = 1$, the two correlations $r_{MZ}$ and $r_{DZ}$ determine the three parameters:

$$a^2 = 2\,(r_{MZ} - r_{DZ}), \qquad c^2 = 2 r_{DZ} - r_{MZ}, \qquad e^2 = 1 - r_{MZ},$$

the narrow-sense heritability being $h^2 = a^2$. The parameters are admissible only in the cone $r_{MZ} \ge r_{DZ} \ge r_{MZ}/2$: $r_{DZ} < r_{MZ}/2$ returns $c^2 < 0$ and signals dominance or epistasis rather than shared environment, while $r_{DZ} > r_{MZ}$ returns $a^2 < 0$. In the submodel with $c = 0$ (the AE model) the identity collapses to $h^2 = r_{MZ}$.

**Estimation and model choice.** Rather than solving the moment equations, fit the parameters by maximizing the multivariate normal likelihood of all observed family vectors, which uses incomplete pairs and unpaired individuals for the means and variances and handles covariates in the mean structure. Nested submodels (AE, with $c = 0$; CE, with $a = 0$) are compared with the full model by the likelihood-ratio statistic $2(\log L_{\text{full}} - \log L_{\text{sub}})$, referred to a $\chi^2$ distribution whose degrees of freedom equal the number of constrained parameters; the most parsimonious model not rejected is reported. Failing to reject $c = 0$ is weak evidence: twin samples of a few hundred pairs have little power to separate $a^2$ from $c^2$, because both enter only through two correlations.

## Depends on

- [Falconer's estimator](../falconer.md)
- [Full-sib covariance in terms of variance components](../../fisher-s-decomposition-of-genetic-variance/cov-full-sibs-eq.md)
- [Log-density of the multivariate Gaussian](../../../../Probability/linear-models-multivariate/gaussian-maximum-likelihood/log-multivariate-gaussian-pdfreal.md)

## Expansion

Monozygotic co-twins share both alleles at every locus, so $\operatorname{Cor}(A_{i1}, A_{i2}) = 1$; dizygotic co-twins and full siblings share one allele in expectation at half the loci, giving the coefficient $1/2$ on $a^2$, the same additive coefficient of relatedness that gives the parent–offspring and sibling covariances in Fisher's decomposition. Both twin types share $C_i$ exactly, by the equal-environments assumption, and nothing else. Subtracting the two correlations removes $c^2$ and leaves $a^2/2$, which is the Falconer doubling $a^2 = 2(r_{MZ} - r_{DZ})$; substituting back gives $c^2$, and the residual is $e^2$. Because $E$ absorbs measurement error, $e^2$ is an upper bound on the true nonshared-environmental variance and $a^2$ and $c^2$ are correspondingly attenuated when the phenotype is noisy; conversely, dominance variance, which contributes $1$ to monozygotic and $1/4$ to dizygotic correlations, is confounded with $a^2$ and $c^2$ and inflates the estimated heritability when ignored. As an illustration, a hair-cortisol phenotype with $r_{MZ} = 0.66$ and $r_{DZ} = 0.42$ lies above the $r_{MZ}/2$ boundary; the AE submodel was not rejected and gave a heritability near $0.7$.

## Sources

- L. Rietschel, F. Streit, G. Zhu, K. McAloney, J. Frank, B. Couvy-Duchesne, S. H. Witt, T. M. Binz, et al., *Hair cortisol in twins: heritability and genetic overlap with psychological variables and stress-system genes*, Scientific Reports 7 (2017), 15351, <https://doi.org/10.1038/s41598-017-11852-3>, PMCID PMC5703444. Methods, "Twin correlations, heritability of HCC, and shared covariance with psychological variables" (structural equation models partitioning variance into additive genetic, shared environmental and unique environmental components, full maximum likelihood using unpaired twins and singletons, AE and CE submodels compared with ACE by likelihood-ratio chi-square tests, covariates in the mean) and Results, "Heritability" (the monozygotic and dizygotic correlations and the resulting heritability estimate). The identification formulas and admissibility cone are standard and derived here.
