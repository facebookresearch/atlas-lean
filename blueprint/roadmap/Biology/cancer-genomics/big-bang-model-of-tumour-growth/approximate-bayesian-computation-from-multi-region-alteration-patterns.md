# Approximate Bayesian computation from multi-region alteration patterns

Let a tumour be sampled at single-gland resolution on two opposite sides, and encode every
subclonal (non-public) alteration by a binary string giving its presence ($1$) or absence ($0$) in
each sampled gland. Alterations present in all sampled glands are public and are excluded, since
they predate the expansion being modelled. The private alterations are classified by their pattern:

- **side-specific:** in all glands of one side only;
- **side-variegated:** in all glands of one side and some glands of the other;
- **variegated:** in a subset of glands from both sides;
- **regional:** in more than one but not all glands of one side only;
- **unique:** in a single gland.

The summary statistics of a data set are (i) the number of distinct binary strings, (ii) the Shannon
index of the binary patterns, (iii) the total number of alterations, (iv) the number of variegated
alterations and (v) the number of side-variegated alterations. Each statistic is standardized to mean
$0$ and standard deviation $1$ over the simulations, and the distance between simulated and observed
data is the average distance over the standardized statistics. With uniform priors on the mutation
rate $\mu$ and the fitness-change scale $\sigma$ of the
[gland-fission model](gland-fission-cellular-automaton-with-gaussian-fitness-changes.md), thousands of
tumours are simulated and sampled like the real one, and the parameter values of the simulations
closest to the data approximate the posterior of $(\mu, \sigma)$ for that patient. The same
simulations record when each alteration arose, which gives the posterior of the tumour size at which
each class of alteration occurred.

## Depends on

- [Gland-fission cellular automaton with Gaussian fitness changes](gland-fission-cellular-automaton-with-gaussian-fitness-changes.md)

## Remarks

The likelihood of the spatial presence patterns under a three-dimensional growth model is intractable,
but simulating the model is easy, so ABC replaces likelihood evaluation with the comparison of summary
statistics. The statistics were chosen because they discriminate early from late alteration timing.
Variegated and side-variegated counts are high only when alterations arose early and were scattered by
the expansion, while regional and unique alterations mark late events. Standardization makes
statistics on different scales comparable in one distance. Simulations on synthetic data with known
parameters showed that the procedure recovers the correct values in most cases.

## Sources

- A. Sottoriva, H. Kang, Z. Ma, T. A. Graham, M. P. Salomon, J. Zhao, P. Marjoram, K. Siegmund,
  M. F. Press, D. Shibata, C. Curtis, "A Big Bang model of human colorectal tumor growth", Nature
  Genetics 47 (2015) 209-216, Results, "Single gland copy number profiles reveal variegation" and
  "Statistical inference verifies the Big Bang predictions", and Online Methods, "Computational
  framework", <https://doi.org/10.1038/ng.3214> (PMC4575589).
