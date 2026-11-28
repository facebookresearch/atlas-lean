# Rank uniformity for tree topologies via distance to a reference tree

In the generative setting of [Nominal coverage of credible intervals under the prior predictive](nominal-coverage-of-credible-intervals-under-the-prior-predictive.md), draw a phylogeny $\theta \sim f_\Theta$, then data $d \sim f_{D\mid\Theta}(\cdot\mid\theta)$, then $L$ trees $\theta'_1, \dots, \theta'_L$ that, given $d$, are independent draws from the exact posterior $f_{\Theta\mid D}(\cdot \mid d)$ and independent of $\theta$. Fix a reference tree $\tau$ on the same taxa, chosen independently of all these draws, and score each tree by its Robinson–Foulds distance $g(\vartheta) = d_{\mathrm{RF}}(\vartheta, \tau)$. Draw independent keys $U_0, \dots, U_L \sim \operatorname{Uniform}(0, 1)$, independent of everything else, and let

$$r = \#\{\, j \le L : (g(\theta'_j), U_j) < (g(\theta), U_0) \,\}$$

in lexicographic order.

**Theorem.** Conditional on $d$ and $\tau$, and hence unconditionally, $r$ is uniformly distributed on $\{0, 1, \dots, L\}$.

Because the Robinson–Foulds distance takes finitely many values, ties among the scores have positive probability and the randomized tie breaking is needed; the strict rank without it need not be uniform. Over $n$ independent replicates, a histogram of ranks should therefore be flat, and the empirical CDF of $r/L$ should follow the discrete-uniform staircase with value $(k+1)/(L+1)$ at $k/L$, not a flat or diagonal line. Systematic departures from the flat histogram are diagnostic: a U shape indicates posteriors that are too narrow, a central hump posteriors that are too wide, and mass piled at one end biased over- or underestimation.

## Depends on

- [Nominal coverage of credible intervals under the prior predictive](nominal-coverage-of-credible-intervals-under-the-prior-predictive.md)
- [Simulation-based calibration: conditional no-ties and randomized ranks](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/simulation-based-calibration-rank-uniformity-und.md)
- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

Conditionally on $d$, the generating tree is itself a posterior draw, so $\theta, \theta'_1, \dots, \theta'_L$ are $L+1$ independent draws from one law; for fixed $\tau$, $g$ is a fixed measurable score, and the randomized-rank theorem gives conditional uniformity, which survives averaging over $d$ and $\tau$. The same argument applies to any scalar summary of a tree, such as the root age; for a continuous summary whose posterior pushforward is atomless the keys can be dropped. The distance to a reference tree extends rank checks to tree topologies, where a coverage interval has no natural meaning. MCMC output is autocorrelated, so the $L$ draws should be thinned to roughly the effective sample size; otherwise the histogram shows spurious structure even for a correct implementation. Choosing a number of bins dividing $L+1$ keeps the expected bin counts equal.

## Sources

- F. K. Mendes, R. Bouckaert, L. M. Carvalho, A. J. Drummond, "How to validate a Bayesian evolutionary model", Systematic Biology 74(1) (2025) 158–175, section on rank-uniformity validation (citing Talts et al. 2018, Theorem 1), Figure 5, and the tree-space extension using the Robinson–Foulds distance, <https://doi.org/10.1093/sysbio/syae064>, PMCID PMC11809579.
- S. Talts, M. Betancourt, D. Simpson, A. Vehtari, A. Gelman, "Validating Bayesian inference algorithms with simulation-based calibration", <https://arxiv.org/abs/1804.06788>, Section 4.1 and Theorem 1.
