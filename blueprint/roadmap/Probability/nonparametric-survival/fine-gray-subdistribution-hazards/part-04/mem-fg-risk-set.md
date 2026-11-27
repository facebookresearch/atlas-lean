# Membership in the Fine–Gray risk set

Let $\iota$ be a set of causes, $n \in \mathbb{N}$, $c \in \iota$ a cause of interest, observed times $X_1, \dots, X_n \in \mathbb{R}$ and statuses $\varepsilon_1, \dots, \varepsilon_n$, where $\varepsilon_l = \mathrm{none}$ means subject $l$ is censored and $\varepsilon_l = \mathrm{some}\ c'$ means subject $l$ fails from cause $c' \in \iota$.

For subjects $i, l \in \{1, \dots, n\}$, subject $l$ belongs to the [Fine–Gray risk set](../part-03/fg-risk-set.md) $R^*(i)$ for cause $c$ at the observed time of subject $i$ if and only if

$$
X_i \le X_l \quad \text{or} \quad \left(X_l < X_i,\ \varepsilon_l \ne \mathrm{none} \text{ and } \varepsilon_l \ne \mathrm{some}\ c\right),
$$

that is, $l$ is still under observation at $X_i$ or failed from a cause other than $c$ before $X_i$.

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509.
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 3, the unnumbered complete-data partial-likelihood display before eq. (2) and the sentence following it defining the risk set $R_i$.
