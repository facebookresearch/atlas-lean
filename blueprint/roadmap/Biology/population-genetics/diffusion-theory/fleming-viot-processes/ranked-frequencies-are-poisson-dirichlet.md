# Ranked masses of the stationary Fleming–Viot measure

This node covers the ranked allele frequencies of the stationary infinitely-many-neutral-alleles model.
The [Dirichlet process](../../../../Probability/bayesian-statistics/dirichlet-process/dirichlet-process.md) $\mathrm{DP}(\theta, \nu_0)$ (parameter $\theta\nu_0$ in the notation of the first
source below), which is the
[stationary law of the Fleming–Viot process](dirichlet-process-stationary-law.md) for $\theta > 0$ and
atomless $\nu_0$, has the series representation
$\sum_i W_i \delta_{Y_i}$ with $Y_i$ independent with law $\nu_0$ and independent of the weights
$W_i = Q_i / \sum_j Q_j$, where the $Q_i$ are the jumps of a gamma process with mean measure
$\theta y^{-1} e^{-y}\,dy$; the decreasingly ranked weights have the Poisson–Dirichlet distribution
with parameter $\theta$ (Kingman, 1975; in Pitman's notation, Poisson–Dirichlet$(0, \theta)$ frequencies are the ranked jumps of a gamma process on $[0, \theta]$ conditioned to have total $1$). When $\nu_0$ has no atoms, the $Y_i$ are almost surely
distinct, so the ranked atom masses of a measure with law $\mathrm{DP}(\theta, \nu_0)$, in particular of the stationary
measure, are Poisson–Dirichlet($\theta$). Ethier
and Kurtz (1981) construct the diffusion of ranked frequencies directly and show that it has a unique
stationary distribution and is reversible and ergodic.

## Depends on

- [Dirichlet process](../../../../Probability/bayesian-statistics/dirichlet-process/dirichlet-process.md)
- [Dirichlet-process stationary law of the Fleming–Viot process](dirichlet-process-stationary-law.md)

## Expansion

A sound expansion defines the Poisson–Dirichlet law from the gamma-process construction, proves the
series representation of the Dirichlet process, and deduces the ranked-mass statement for diffuse
$\nu_0$; the ranked-frequency diffusion and its stationary law are a separate page.

## Sources

- O. Papaspiliopoulos, M. Ruggiero and D. Spanò, "Conjugacy properties of time-evolving Dirichlet and gamma random measures", Electronic Journal of Statistics 10 (2016), 3452–3489, <https://doi.org/10.1214/16-EJS1194>, preprint <https://arxiv.org/abs/1607.02896>, Section 2.1.1, equation (8) (series representation of the Dirichlet process).
- J. Pitman, *Combinatorial Stochastic Processes*, Lecture Notes in Mathematics 1875, Springer (2006),
  preprint <http://works.bepress.com/jim_pitman/1>, Section 2.5 "Limits of Gibbs partitions",
  Theorem 2.4 and the discussion after it, and Section 3.1 "The Chinese restaurant process".
- J. F. C. Kingman, "Random discrete distributions", Journal of the Royal Statistical Society, Series B
  37 (1975), 1–15, <https://doi.org/10.1111/j.2517-6161.1975.tb01024.x>.
- S. N. Ethier and T. G. Kurtz, "The infinitely-many-neutral-alleles diffusion model", Advances in
  Applied Probability 13 (1981), 429–452, <https://doi.org/10.2307/1426779>.
