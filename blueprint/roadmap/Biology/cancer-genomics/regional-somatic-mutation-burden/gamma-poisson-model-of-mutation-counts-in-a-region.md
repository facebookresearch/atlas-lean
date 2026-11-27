# Gamma-Poisson model of mutation counts in a region

Let $R$ be a genomic region whose neutral somatic mutation rate is uncertain, with predicted mean
$\mu_R > 0$ and variance $\sigma_R^2 > 0$, and put

$$\alpha_R = \frac{\mu_R^2}{\sigma_R^2}, \qquad \theta_R = \frac{\sigma_R^2}{\mu_R},$$

the shape and scale of the gamma distribution with that mean and variance. Let
$p_{R,\,aX \to Yb}$ be the probability that a mutation in $R$ falls at a given position and changes
the base $X$ in context $a\,X\,b$ into $Y$, normalized so that the probabilities of all possible
mutations in $R$ sum to $1$, and let $C_{\mathrm{SNV}} > 0$ scale for the size of the cohort under
study relative to the cohort the rates were trained on. For a set $I$ of candidate single-nucleotide
variants in $R$, with $M_{i,\,aX \to Yb}$ the number of observed variants of each type at each
position, the marginal law of the total count is negative binomial,

$$\sum_{I} M_{i,\,aX \to Yb} \ \sim\
\mathrm{NegativeBinomial}\Bigl(\alpha_R,\ \frac{1}{1 + C_{\mathrm{SNV}}\,\theta_R \sum_{I} p_{R,\,aX \to Yb}}\Bigr),$$

the gamma-Poisson mixture in which the Poisson rate for the set $I$ is the regional rate thinned by
the context probabilities. An excess of observed mutations over this null is evidence of positive
selection on the set $I$; the $p$-value is the upper tail of the distribution, and the $p$-value for
a union of regions is obtained by convolving their negative binomial distributions.

## Depends on

- [Negative binomial mass function with real shape](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-pmf.md)

## Proof depends on

- [Greenwood–Yule](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/gamma-poisson-mixture/poisson-mixture-real-gamma-measure.md)
- [Mean parametrization of the negative binomial law](../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real-eq-neg-binomial-pmf.md)
- [Scaling a gamma random variable](../../../Probability/distributions/continuous/gamma-distribution/gamma-scaling/gamma-measure-map-const-mul.md)

## Remarks

The two factors separate two scales. The kilobase-scale mean and variance say how many neutral
mutations a 10-50 kb window should carry, given epigenetic covariates such as chromatin state;
the context probabilities say how those mutations distribute over individual positions. Treating
the regional rate as gamma-distributed rather than known turns the Poisson count into a negative
binomial one, which is what gives the test calibrated behaviour when regional rate prediction is
imperfect. Because every parameter except $C_{\mathrm{SNV}}$ is fixed once the model is trained,
testing an arbitrary user-specified set of mutations costs only a table lookup, which is what makes
scanning small sets, such as predicted cryptic splice variants, feasible genome-wide.

## Sources

- M. A. Sherman, A. U. Yaari, O. Priebe, F. Dietlein, P.-R. Loh, B. Berger, "Genome-wide mapping of
  somatic mutation rates uncovers drivers of cancer", Nature Biotechnology 40 (2022) 1634-1643,
  Methods, "Modeling mutation counts over an arbitrary set of positions",
  <https://doi.org/10.1038/s41587-022-01353-8> (PMC9646522).
