# Complement of the subdistribution risk event

Let $\Omega$ and $\iota$ be sets, $T : \Omega \to \mathbb{R}$ a failure time, $J : \Omega \to \iota$ a failure cause and $c \in \iota$ a cause. For $t \in \mathbb{R}$ the [subdistribution risk event](../part-07/subdist-risk-set.md) is

$$
R_c(t) = \{\omega : T(\omega) \ge t\} \cup \{\omega : T(\omega) < t,\ J(\omega) \ne c\}.
$$

For every $t \in \mathbb{R}$, the complement of the risk event is the event of a cause-$c$ failure before $t$:

$$
\Omega \setminus R_c(t) = \{\omega : T(\omega) < t,\ J(\omega) = c\}.
$$

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509.
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 1, eq. (1) and the integrated CIF formula.
