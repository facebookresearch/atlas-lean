# Log-linear mixed model for per-feature microbiome association

Let $c_{fs} \ge 0$ be the abundance (count or relative count) of microbial feature $f = 1, \dots, p$ in
sample $s$, let subject $j(s)$ be the individual from whom sample $s$ was taken, and let
$x_s \in \mathbb{R}^q$ be the fixed-effect metadata (phenotypes and covariates) of the sample.

1. **Total sum scaling.** Normalize each sample to relative abundances
   $a_{fs} = c_{fs} / \sum_{f'} c_{f's}$.
2. **Log transform.** Set $y_{fs} = \log(a_{fs} + \delta_f)$, where the pseudocount $\delta_f > 0$ is
   half the smallest nonzero relative abundance of the feature.
3. **Per-feature model.** For each feature separately fit the linear mixed model

$$y_{fs} = \beta_{f0} + x_s^{\top}\beta_f + z_s^{\top} b_{f,\,j(s)} + \varepsilon_{fs},
\qquad b_{f,\,j} \sim \mathcal{N}(0, \Sigma_f),\quad \varepsilon_{fs} \sim \mathcal{N}(0, \sigma_f^2),$$

   with random effects $b_{f,j}$ shared by all samples of subject $j$ (design $z_s$, usually a random
   intercept), independent across subjects and of the errors. Without repeated measures the random
   effect is dropped and the model is ordinary least squares.
4. **Inference.** For each feature-coefficient pair $(f, k)$, test $H_0 : \beta_{fk} = 0$, and adjust
   all $p \times q$ nominal $p$-values together with the Benjamini-Hochberg procedure, reporting the
   pairs whose $q$-value is below a chosen level (0.25 in the source's multi-omics analysis).

## Remarks

Microbiome profiles are compositional, sparse and far from normal, which tempts count models
(negative binomial, zero-inflated, compound Poisson). In the source's simulations with realistic
synthetic communities, those models often inflated the false discovery rate, while the log-linear
model on normalized data kept it near target and stayed well powered, especially with several
correlated covariates. The random subject effect absorbs the within-subject correlation of
longitudinal samples. Without it, repeated samples from the same person count as independent, which
makes the inference anti-conservative. Low-information features, such as those with more than 90%
zeros or very low variance, are usually filtered out before fitting.

## Sources

- H. Mallick, A. Rahnavard, L. J. McIver, et al., "Multivariable association
  discovery in population-scale meta-omics studies", PLoS Computational Biology 17 (2021) e1009442,
  "Design and implementation", the repeated-measures simulations and the HMP2 analysis (Fig 5),
  <https://doi.org/10.1371/journal.pcbi.1009442> (PMC8714082).
