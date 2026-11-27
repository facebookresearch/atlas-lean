# Failure time in the proportional subdistribution hazards family

On the sample space $\mathbb{R}$ of the latent variable $\omega$, the failure time is

$$
T(\omega) = \begin{cases} \dfrac{\omega}{1-\omega} & \text{if } \omega < 1,\\ 1 & \text{if } \omega \ge 1. \end{cases}
$$

The first case is a failure from the cause of interest and the second a failure from the competing cause (see the [failure cause](ph-cause.md)). The denominator $1 - \omega$ is positive in the first case.

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509 (for the proportional subdistribution hazards model).
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 1, eq. (1) and the integrated CIF formula (for the model; the latent exponential law, threshold and cause maps, and baseline $(1+t)^{-2}$ here are a construction satisfying (1), not a formula from the paper).
