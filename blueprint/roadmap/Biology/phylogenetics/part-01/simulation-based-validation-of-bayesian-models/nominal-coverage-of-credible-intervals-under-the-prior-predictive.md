# Nominal coverage of credible intervals under the prior predictive

Let $f_\Theta$ be a prior density on a parameter $\Theta$ and $f_{D\mid\Theta}$ a likelihood, defining the joint law $\theta \sim f_\Theta$, $d \mid \theta \sim f_{D\mid\Theta}(\cdot \mid \theta)$ and the posterior $f_{\Theta\mid D}(\theta \mid d) = f_{D\mid\Theta}(d\mid\theta) f_\Theta(\theta)/f_D(d)$. For $\alpha \in (0,1)$, let $I_\alpha(d)$ be any measurable set-valued map with posterior credibility exactly $\alpha$,

$$\int_{I_\alpha(d)} f_{\Theta\mid D}(\theta \mid d)\, d\theta = \alpha \quad \text{for every } d,$$

for example the highest-posterior-density (shortest) interval of a continuous scalar parameter.

**Proposition.** If $(\theta, d)$ is drawn from the joint generative model, then $\Pr\big(\theta \in I_\alpha(d)\big) = \alpha$. Consequently, for $n$ independent replicates $(\theta_i, d_i)$, the number of indices with $\theta_i \in I_\alpha(d_i)$ is $\operatorname{Binomial}(n, \alpha)$. For $n = 100$ and $\alpha = 0.95$, the central $95\%$ range of this count is $90$ to $99$.

Coverage holds only on average over the prior: it need not hold for parameter values chosen by hand, and a coverage test computed on a fixed grid of "true" values is not a test of correctness.

## Expansion

By the tower property, $\Pr(\theta \in I_\alpha(d)) = \mathbb{E}_d\big[\Pr(\theta \in I_\alpha(d) \mid d)\big] = \mathbb{E}_d[\alpha] = \alpha$, because conditionally on $d$ the generating $\theta$ is distributed according to the exact posterior. Independence across replicates gives the binomial law. In practice $I_\alpha(d_i)$ is estimated from $L$ MCMC samples, so the test also detects sampler errors. Coverage within the binomial bounds is necessary but not sufficient for correctness: mild misspecification (e.g. rejection sampling of simulated trees by taxon count) can pass coverage when a parameter's posterior location responds weakly to the data, whereas rank-based checks may still flag it. For tree topologies, the analogous property is that among all clades sampled with posterior support near $q$, a fraction about $q$ are true clades.

## Sources

- F. K. Mendes, R. Bouckaert, L. M. Carvalho, A. J. Drummond, "How to validate a Bayesian evolutionary model", Systematic Biology 74(1) (2025) 158–175, coverage-validation section (HPD definition, coverage statement, Figure 3 and Table 2) and the clade-coverage procedure, <https://doi.org/10.1093/sysbio/syae064>, PMCID PMC11809579.
