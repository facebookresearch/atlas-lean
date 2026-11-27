# Integrating over genealogies versus plug-in inference

Inference that fixes one estimated genealogy and treats it as observed discards the uncertainty in the genealogy that integrated inference carries. For a square-integrable statistic $h$ of the data $D$ and the genealogy $g$, the law of total variance gives $\mathrm{Var}(h) = E[\mathrm{Var}(h \mid g)] + \mathrm{Var}(E[h \mid g])$, while a variance computed at a fixed estimate $\hat g$ is $\mathrm{Var}(h \mid g = \hat g)$, which in general differs from both terms and in particular omits the between-genealogy term. By Jensen's inequality, if $f$ is convex and $E[\hat g \mid g] = g$, then $E[f(\hat g) \mid g] \ge f(g)$, with strict inequality when $f$ is strictly convex and $\hat g$ is not almost surely constant given $g$; a plug-in estimate $f(\hat g)$ is then biased upward for $f(g)$. Stern, Wilton and Nielsen (2019, Results and Discussion) illustrate both effects for the selection coefficient $s$: importance-sampling estimates that integrate over sampled genealogies have larger variance than estimates from the true local tree, reflecting uncertainty in the tree (their Figure 5 against Supplementary Figure S1); point estimates of $s$, of its timing and of the frequency trajectory were strongly affected by biases of the genealogy sampler, which produced more recent coalescences than the true trees (Supplementary Figure S5); and scalable genealogy-inference methods return a point estimate of the local tree without its uncertainty.

## Depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)
- [Tower property of conditional expectation](../../../../Probability/foundations/conditional-expectation/tower-property/tower-property.md)
- [Total variance splits into true-score and error variance](../../../../Probability/not-yet-classified/part-15/true-score/variance-eq-variance-cond-exp-add-varian.md)

## Expansion

1. The decomposition for a square-integrable statistic of data and genealogy, from the general laws of total expectation and total variance.
2. Plug-in estimates $f(\hat g)$ and their bias for nonlinear $f$.
3. An explicit example: the plug-in estimate of $\theta$ from the total length of an estimated tree against the estimate that integrates over genealogies.
4. The increase in variance and the bias from the genealogy sampler in genealogy-based selection inference, as reported by Stern, Wilton and Nielsen.

## Sources

- A. J. Stern, P. R. Wilton and R. Nielsen, An approximate full-likelihood method for inferring selection and allele frequency trajectories from DNA sequence data, PLoS Genet. 15 (2019), e1008384, Results (Figure 5, Supplementary Figures S1 and S5) and Discussion. <https://doi.org/10.1371/journal.pgen.1008384>
