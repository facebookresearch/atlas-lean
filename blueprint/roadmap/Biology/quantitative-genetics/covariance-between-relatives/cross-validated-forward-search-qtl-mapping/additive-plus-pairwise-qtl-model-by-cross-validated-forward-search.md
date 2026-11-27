# Additive-plus-pairwise QTL model selected by cross-validated L0 forward search

Let $N$ haploid segregants of a cross between two parental strains have genotypes $g_{ij} \in \{0, 1\}$ (BY or RM allele) at SNPs $j$ and a measured phenotype $y_i$ (here competitive fitness). The **additive-plus-pairwise QTL model** with lead SNPs $Q = \{q_1, \dots, q_K\}$ and interacting pairs $P \subseteq \binom{Q}{2}$ is

$$y_i = \mu + \sum_{k=1}^{K} \beta_{q_k}\, g_{i q_k} + \sum_{\{q, q'\} \in P} \gamma_{q q'}\, g_{iq}\, g_{iq'} + \varepsilon_i ,$$

fitted by least squares. The model is selected by an L0-penalized forward search:

1. **Additive stage.** Starting from the empty model, repeatedly add the SNP that most improves the fit, and after each addition jointly re-optimize all effect sizes $\beta$ and all lead-SNP positions. On each of the cross-validation splits (for example $90\%$ training, $10\%$ test), stop when the test-set performance first declines; the average number of steps at which this happens defines an L0 penalty on $K$, i.e. on the number of QTL, which is then used to fit the final model on all data.
2. **Pairwise stage.** Restricting candidates to pairs of loci already in the additive model, run the same forward search over interaction terms, re-optimizing $\beta$ and $\gamma$ at each step, with a second L0 penalty on $|P|$ chosen by cross-validation.
3. **Localization.** For each lead SNP, report a Bayesian $95\%$ credible interval for the causal position rather than a LOD-drop interval.

## Depends on

- [Ordinary least-squares estimator](../../../../Probability/linear-models-multivariate/ordinary-least-squares/sampling-properties-of-the-ordinary-least-square/ols-estimator.md)

## Expansion

Classical forward stepwise regression adds SNPs while a $p$-value or LOD score exceeds a genome-wide threshold, but the selected statistics do not follow their nominal $F$ or $\chi^2$ laws after selection, so the procedure produces false positives, especially at large sample size and under strong linkage. Terminating by held-out prediction instead adds a QTL only when its expected contribution to phenotypic variance exceeds the bias and variance introduced by the greedy search, which shrink as $N$ grows; the procedure therefore tends to miss loci of very small effect rather than invent loci. Restricting interactions to additive loci loses little, because a pair with an interaction but no main effects still produces background-averaged marginal associations at each locus, which bring both loci into the additive model; the spurious additive effects then shrink once the interaction term is added. Applied to about $100{,}000$ barcoded yeast segregants phenotyped in $18$ environments by bulk barcode sequencing, the method resolves highly polygenic architectures with hundreds of pairwise interactions per trait.

## Sources

- A. N. Nguyen Ba, K. R. Lawrence, A. Rego-Costa, S. Gopalakrishnan, D. Temko, F. Michor and M. M. Desai, "Barcoded bulk QTL mapping reveals highly polygenic and epistatic architecture of complex traits in yeast", *eLife* 11 (2022), e73983, Results sections "Modified stepwise cross-validated forward search approach to mapping QTL" and "Epistasis", <https://doi.org/10.7554/eLife.73983> (PMC8979589).
