# The subdistribution hazard equals the limit whenever the limit exists

Let $(\Omega, \mathcal{F})$ be a measurable space with a measure $P$ (not assumed finite), $\iota$ a set, $T : \Omega \to \mathbb{R}$, $J : \Omega \to \iota$, $c \in \iota$ and $t, l \in \mathbb{R}$. Suppose the [subdistribution hazard exists at $t$ with value $l$](../part-04/has-subdist-hazard-at.md), that is,

$$
\lim_{h \to 0^+} \frac{1}{h} P\left(t \le T < t+h,\ J = c \mid T \ge t \text{ or } (T < t,\ J \ne c)\right) = l,
$$

with the conditional measure as defined there and the [quotient](../part-07/subdist-hazard-quotient.md) as defined on its page. Then the [subdistribution hazard](../part-07/subdist-hazard.md) $\lambda^*_c(t)$, defined as this right limit (and as an arbitrary fixed value when the limit does not exist), equals $l$.

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509.
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 1, eq. (1) and the integrated CIF formula.
