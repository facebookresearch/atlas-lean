# Rank uniformity in simulation-based calibration

In the generative setting of [Nominal coverage of credible intervals under the prior predictive](nominal-coverage-of-credible-intervals-under-the-prior-predictive.md), draw $\theta \sim f_\Theta$, then $d \sim f_{D\mid\Theta}(\cdot\mid\theta)$, then $L$ draws $\theta'_1, \dots, \theta'_L$ independently from the posterior $f_{\Theta\mid D}(\cdot \mid d)$. For a scalar functional $g$ (a parameter, the root age of a tree, or a distance to a fixed reference tree), define the rank
$$r = \#\{\, j \le L : g(\theta'_j) < g(\theta) \,\}.$$

**Theorem.** If $g(\theta)$ has a continuous distribution (so ties have probability zero), then $r$ is uniformly distributed on $\{0, 1, \dots, L\}$.

Hence, over $n$ independent replicates, a histogram of ranks (or the empirical CDF of $r/L$) should be flat. Systematic departures are diagnostic: a U-shaped histogram indicates posteriors that are too narrow (underdispersed), a central hump indicates posteriors that are too wide, and mass piled at one end indicates biased over- or underestimation.

## Depends on

- [Nominal coverage of credible intervals under the prior predictive](nominal-coverage-of-credible-intervals-under-the-prior-predictive.md)

## Expansion

Conditionally on $d$, the generating $\theta$ is itself a draw from the posterior, so $\theta, \theta'_1, \dots, \theta'_L$ are $L+1$ exchangeable draws from the same continuous law; the position of $g(\theta)$ among the $L+1$ values is therefore uniform, and this conditional uniformity survives averaging over $d$. MCMC output is autocorrelated, so the $L$ draws should be thinned to roughly the effective sample size; otherwise the histogram shows spurious structure even for a correct implementation. Choosing a number of bins dividing $L+1$ keeps the expected bin counts equal. Applying $g = $ Robinson–Foulds distance to a random reference tree extends the check to tree topologies, where a coverage interval has no natural meaning.

## Sources

- F. K. Mendes, R. Bouckaert, L. M. Carvalho, A. J. Drummond, "How to validate a Bayesian evolutionary model", Systematic Biology 74(1) (2025) 158–175, section on rank-uniformity validation (citing Talts et al. 2018, Theorem 1), Figure 5, and the tree-space extension using the Robinson–Foulds distance, <https://doi.org/10.1093/sysbio/syae064>, PMCID PMC11809579.
