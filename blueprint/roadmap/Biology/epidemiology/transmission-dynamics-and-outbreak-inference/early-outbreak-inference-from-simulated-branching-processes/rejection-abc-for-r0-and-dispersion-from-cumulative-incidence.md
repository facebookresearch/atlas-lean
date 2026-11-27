# Rejection ABC for the reproduction number and dispersion from cumulative incidence

Let $\vartheta = (R_0, k, D, n)$ collect the basic reproduction number, the negative-binomial dispersion, the mean generation interval and the number of index cases, with a prior $\pi$ on a finite grid, and let the index-case introduction dates be drawn uniformly from a window. For each $\vartheta$ the branching-process model defines the law $P_\vartheta$ of the cumulative incidence $C(t^*)$ at an observation date $t^*$. Suppose the data consist only of the interval statement $C(t^*) \in A = [c_-, c_+]$.

Rejection approximate Bayesian computation draws $\vartheta \sim \pi$, simulates $C(t^*)$ under $P_\vartheta$, and keeps $\vartheta$ if $C(t^*) \in A$. Then:

1. The accepted values are exact draws from the posterior given the interval observation,

$$\pi(\vartheta \mid C(t^*) \in A) = \frac{\pi(\vartheta)\, P_\vartheta(C(t^*) \in A)}{\sum_{\vartheta'} \pi(\vartheta')\, P_{\vartheta'}(C(t^*) \in A)}.$$

2. Equivalently, with $M$ simulations at each grid point, the acceptance proportion at $\vartheta$ is an unbiased and consistent estimator of the likelihood $P_\vartheta(C(t^*) \in A)$, and normalizing these proportions times the prior estimates the posterior on the grid.
3. Marginal posteriors of $R_0$ and $k$ follow by summing over the other coordinates.

## Depends on

- [Superposition of single-index-case branching epidemics](superposition-of-single-index-case-branching-epidemics.md)

## Proof depends on

- [Rejection ABC returns the tolerance-conditioned posterior](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/rejection-sampling/abc-rejection-target-law-and-zero-tolerance-disc.md)

## Proof sketch

The acceptance event has probability $\pi(\vartheta) P_\vartheta(C(t^*) \in A)$ for each grid point, so conditioning on acceptance gives Bayes' rule with the interval likelihood (the case $S = C(t^*)$, $s_{\rm obs} = (c_- + c_+)/2$, $\varepsilon = (c_+ - c_-)/2$ of rejection ABC with a tolerance); unlike distance-based ABC there is no tolerance approximation, because the observation itself is an interval. For the early Wuhan epidemic the grid had 22 values of $R_0$ in $[0.8, 5]$, 20 log-spaced values of $k$ in $[0.01, 10]$, 8 mean generation intervals between 7 and 14 days (gamma with shape 2), and 6 values of $n$ between 1 and 50, with introduction dates uniform over two weeks around 27 November 2019. Single-index epidemics were simulated 1,000 times per combination and combined 100 times per combination by superposition. Accepting epidemics with 1,000 to 9,700 cases by 18 January 2020 gave $R_0 \approx 2.2$ (90% high-density interval 1.4–3.8) and a wide posterior for $k$ (median 0.54, interval 0.014–6.95) that disfavours very strong superspreading. The interval data inform $R_0$ much more than $k$, because many dispersion values produce similar cumulative sizes.

## Sources

- J. Riou and C. L. Althaus, "Pattern of early human-to-human transmission of Wuhan 2019 novel coronavirus (2019-nCoV), December 2019 to January 2020", Eurosurveillance 25(4) (2020), 2000058, sections "Simulating early outbreak trajectories" and results (Figures 1–3), <https://doi.org/10.2807/1560-7917.ES.2020.25.4.2000058>, PMCID: PMC7001239.
