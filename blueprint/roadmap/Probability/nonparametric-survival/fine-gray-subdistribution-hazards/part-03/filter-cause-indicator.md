# Subjects selected by the cause-specific event indicator

Let $\iota$ be a set of causes, $n \in \mathbb{N}$, $c \in \iota$ a cause of interest and statuses $\varepsilon_1, \dots, \varepsilon_n$, where $\varepsilon_l = \mathrm{none}$ means subject $l$ is censored and $\varepsilon_l = \mathrm{some}\ c'$ means subject $l$ fails from cause $c' \in \iota$.

Let $\delta_i$ be the [cause-$c$ event indicator](cause-indicator.md), true exactly when $\varepsilon_i = \mathrm{some}\ c$. Then the set of subjects with $\delta_i = \mathrm{true}$ is the set of cause-$c$ failures:

$$
\{i \in \{1, \dots, n\} : \delta_i = \mathrm{true}\} = \{i \in \{1, \dots, n\} : \varepsilon_i = \mathrm{some}\ c\}.
$$

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509.
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 3, the unnumbered complete-data partial-likelihood display before eq. (2) and the sentence following it defining the risk set $R_i$.
