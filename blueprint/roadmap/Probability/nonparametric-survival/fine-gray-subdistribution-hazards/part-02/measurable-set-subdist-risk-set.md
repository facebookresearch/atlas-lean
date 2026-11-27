# Measurability of the subdistribution risk event

Let $(\Omega, \mathcal{F})$ be a measurable space, $\iota$ a set, $T : \Omega \to \mathbb{R}$ a measurable failure time, $J : \Omega \to \iota$ a failure cause and $c \in \iota$ a cause such that the event $\{\omega : J(\omega) = c\}$ is measurable (measurability of $J$ itself is not assumed).

For every $t \in \mathbb{R}$, the [subdistribution risk event](../part-07/subdist-risk-set.md)

$$
R_c(t) = \{\omega : T(\omega) \ge t\} \cup \{\omega : T(\omega) < t,\ J(\omega) \ne c\}
$$

is measurable.

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509.
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 1, eq. (1) and the integrated CIF formula.
