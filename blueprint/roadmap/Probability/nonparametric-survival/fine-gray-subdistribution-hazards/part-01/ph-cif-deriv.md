# Derivative of the closed-form cumulative incidence of the proportional subdistribution hazards family

For $\theta, t \in \mathbb{R}$,

$$
\phi'(\theta, t) = \frac{\theta}{(1+t)^2} \exp\left(-\theta \frac{t}{1+t}\right),
$$

with real division ($a/0 = 0$), so $\phi'(\theta, -1) = 0$. It is the derivative in $t$ of the [closed-form cumulative incidence](ph-cif.md) away from $t = -1$, as stated in the [derivative identity](has-deriv-at-ph-cif.md).

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509 (for the proportional subdistribution hazards model).
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 1, eq. (1) and the integrated CIF formula (for the model; the latent exponential law, threshold and cause maps, and baseline $(1+t)^{-2}$ here are a construction satisfying (1), not a formula from the paper).
