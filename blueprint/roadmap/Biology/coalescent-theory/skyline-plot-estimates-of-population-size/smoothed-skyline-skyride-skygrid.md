# Smoothed skyline models: skyride and skygrid

The Bayesian skyride of Minin, Bloomquist and Suchard (2008) keeps the effective size constant on each intercoalescent interval, transforms the interval sizes to $\gamma_k = \log\theta_k$ (equation (6)), and places on $\gamma = (\gamma_2, \dots, \gamma_n)$ a Gaussian Markov random field prior that penalizes differences between adjacent components with an overall precision $\tau$ and distances $\delta_k$ between adjacent sites (equation (8)). The prior is time-aware: $\delta_k$ are the distances between the midpoints of consecutive intervals (equation (9)), so changes between short consecutive intervals are penalized more than changes between long ones; $\tau$ receives a gamma prior (equation (10)), with $\alpha = \beta = 0.001$ in their examples. The skygrid of Gill et al. (2013) instead lets the piecewise-constant size change at pre-specified grid points, typically equally spaced up to a cutoff beyond which the size is constant, places a GMRF prior on the log sizes that does not depend on the genealogy, and bases inference on several unlinked loci, each with its own genealogy; in their simulations, more loci reduce both the bias and the width of the credible intervals.

## Depends on

- [Grouped and Bayesian skyline models](../../../Biology/coalescent-theory/skyline-plot-estimates-of-population-size/grouped-skyline-and-bayesian-skyline.md)

## Expansion

1. The piecewise-constant coalescent likelihood on intercoalescent intervals or on a fixed grid.
2. The Gaussian Markov random field prior on log sizes, uniform or time-aware, with precision $\tau$.
3. Propriety of the posterior with the gamma prior on $\tau$, and the limits $\tau \to \infty$ (a constant size) and $\tau \to 0$ (independent interval estimates).
4. The multi-locus skygrid likelihood as a product over unlinked loci, and the independence of its prior from the genealogy.

## Sources

- V. N. Minin, E. W. Bloomquist and M. A. Suchard, Smooth skyride through a rough skyline: Bayesian coalescent-based inference of population dynamics, Mol. Biol. Evol. 25 (2008), 1459–1471, section "Temporally smoothed piecewise demographic model", equations (6)–(10). <https://doi.org/10.1093/molbev/msn090>
- M. S. Gill, P. Lemey, N. R. Faria, A. Rambaut, B. Shapiro and M. A. Suchard, Improving Bayesian population dynamics inference: a coalescent-based model for multiple loci, Mol. Biol. Evol. 30 (2013), 713–724, sections "New Approaches" and "Simulation Studies". <https://doi.org/10.1093/molbev/mss265>
