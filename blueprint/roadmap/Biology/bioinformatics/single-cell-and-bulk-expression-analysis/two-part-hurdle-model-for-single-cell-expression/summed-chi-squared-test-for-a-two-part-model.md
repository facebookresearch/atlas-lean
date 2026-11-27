# Summed chi-squared test for a two-part model

Let $T^D_g$ and $T^C_g$ be the likelihood-ratio (or Wald) statistics for the same linear hypothesis on the discrete and the continuous component of a two-part hurdle model for gene $g$, with $d_D$ and $d_C$ degrees of freedom respectively. If the two components are conditionally independent given the covariates, then under the null hypothesis and the usual regularity conditions

$$T^D_g \xrightarrow{d} \chi^2_{d_D}, \qquad T^C_g \xrightarrow{d} \chi^2_{d_C}, \qquad T^D_g + T^C_g \xrightarrow{d} \chi^2_{d_D + d_C},$$

so the combined statistic $T_g = T^D_g + T^C_g$ tests the hypothesis in both components simultaneously with $d_D + d_C$ degrees of freedom. Applying the test over genes $g = 1,\dots,N$ gives $p$-values that may be adjusted for multiplicity by a false-discovery-rate procedure.

## Depends on

- [Two-part hurdle model for single-cell expression](hurdle-model-for-single-cell-expression.md)

## Proof depends on

- [Chi-square moment generating functions multiply by adding degrees](../../../../Probability/distributions/continuous/chi-square-distribution/prod-mgf-chi-square-measure-eq-mgf-sum.md)

## Proof sketch

The sum of independent chi-squared variables is chi-squared with the degrees of freedom added, which is immediate from the moment generating function $(1-2t)^{-d/2}$ for $t < 1/2$. Independence is supplied by the model: the detection indicator and the positive expression level are conditionally independent given the design, so the two score or likelihood-ratio statistics are asymptotically independent. This is what lets a change in the proportion of expressing cells and a change in the conditional mean be detected by one test, rather than by two tests whose combination would need a correction. Using a variance estimate shrunk across genes in the continuous part leaves the asymptotic calibration intact while stabilizing genes expressed in few cells.

## Sources

- Finak G, McDavid A, Yajima M, et al. MAST: a flexible statistical framework for assessing transcriptional changes and characterizing heterogeneity in single-cell RNA sequencing data. *Genome Biology* 16:278 (2015), Methods, "Testing for differential expression". DOI <https://doi.org/10.1186/s13059-015-0844-5>. PMCID PMC4676162.
