# Full multi-context expression predictor from shared and specific genetic components

Fix a gene $j$ with cis-genotype matrix $G_j\in\mathbb R^{I\times m}$ and covariate-residualized, standardized expression in $C$ contexts, decomposed into a shared component $E^{\mathrm{Shared}}_j$ and specific components $E^{\mathrm{Specific}}_{jc}$ as in the between- and within-individual decomposition. The predictor is built in three steps.

1. Fit cross-validated elastic-net regressions

$$E^{\mathrm{Shared}}_j=\alpha^{\mathrm{Shared}}+G_j\beta+\varepsilon^{\mathrm{Shared}},\qquad E^{\mathrm{Specific}}_{jc}=\alpha^{\mathrm{Specific}}_c+G_j\gamma_c+\varepsilon^{\mathrm{Specific}}_c,$$

one for the shared component and one for each of the $C$ specific components.
2. Form the genetic predictors $\hat E^{\mathrm{Sh}}_{j}=\hat\alpha^{\mathrm{Shared}}+G_j\hat\beta$ and $\hat E^{\mathrm{Sp}}_{jc}=\hat\alpha^{\mathrm{Specific}}_c+G_j\hat\gamma_c$.
3. For each context fit the ordinary least-squares recombination

$$E_{jc}=\alpha^{\mathrm{Full}}_c+\hat E^{\mathrm{Sh}}_{j}\,w^{\mathrm{Sh}}_{jc}+\hat E^{\mathrm{Sp}}_{jc}\,w^{\mathrm{Sp}}_{jc}+\varepsilon_{jc}.$$

The full predictor of context $c$ is linear in genotype with SNP weights $\hat w^{\mathrm{Sh}}_{jc}\hat\beta+\hat w^{\mathrm{Sp}}_{jc}\hat\gamma_c$, so it can be passed to a summary-statistic transcriptome-wide association test like any single-context weight vector. A component (shared or specific) is declared heritable by a one-degree-of-freedom likelihood-ratio test of its predictor against the intercept-only model, and the full model by a two-degree-of-freedom test.

## Depends on

- [Between- and within-individual decomposition of multi-context expression](between-and-within-individual-decomposition-of-multi-context-expression.md)
- [Ordinary least-squares estimator](../../../../../Probability/linear-models-multivariate/ordinary-least-squares/sampling-properties-of-the-ordinary-least-square/ols-estimator.md): the recombination step

## Expansion

The recombination step is needed because the specific component is a deviation from the individual mean: its weights $\hat\gamma_c$ estimate $\gamma_c-\bar\gamma$, not the effect on the observed expression of context $c$, so their sign and scale must be recalibrated against $E_{jc}$. Because the shared and specific training targets are orthogonal, the specific predictor is constructed to carry little of the shared genetic signal, which is what makes it usable for locating the relevant context of a trait association. The linearity of the final weights is immediate from substituting step 2 into step 3.

In the source, the tests across genes, contexts and the three model types are controlled by a hierarchical false-discovery procedure on the tree gene, context, model; that procedure is taken from earlier work and is not restated here.

## Sources

- M. Thompson, M. G. Gordon, A. Lu, A. Tandon, E. Halperin, A. Gusev, C. J. Ye, B. Balliu and N. Zaitlen, "Multi-context genetic modeling of transcriptional regulation resolves novel disease loci", Nature Communications 13 (2022), 5704, Methods ("A formal description of CONTENT", Equations (6) to (10), and "Controlling the false discovery rate across contexts"), <https://doi.org/10.1038/s41467-022-33212-0> (PMC9519579).
