# Strong ignorability

For a measure $\mu$ on $\Omega$, a treatment event $T$, potential outcomes $V$ and a variable $W$, treatment is strongly ignorable given $W$ for $V$ if $T$ is [conditionally independent](cond-indep-discrete.md) of $V$ given $W$ and overlap holds: the [propensity](propensity.md) satisfies $0 < e(w) < 1$ for every value $w$ with $\mu(W = w) \ne 0$.

## Background

- [The back-door adjustment](../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/backdoor-adjustment.md):
  the graphical criterion that yields the same adjustment formula from a causal diagram.

## Sources

- Paul R. Rosenbaum and Donald B. Rubin, *The central role of the propensity score in observational studies for causal effects*, Biometrika 70 (1983), no. 1, 41–55, DOI 10.1093/biomet/70.1.41.
