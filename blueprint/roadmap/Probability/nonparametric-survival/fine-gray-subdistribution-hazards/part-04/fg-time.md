# Observed times with each competing-event time replaced by the sum of the absolute observed times

Let $\iota$ be a set of causes, $n \in \mathbb{N}$, $c \in \iota$ a cause of interest, observed times $X_1, \dots, X_n \in \mathbb{R}$ and statuses $\varepsilon_1, \dots, \varepsilon_n$, where $\varepsilon_l = \mathrm{none}$ means subject $l$ is censored and $\varepsilon_l = \mathrm{some}\ c'$ means subject $l$ fails from cause $c' \in \iota$.

Subject $l$ has a competing event when $\varepsilon_l \ne \mathrm{none}$ and $\varepsilon_l \ne \mathrm{some}\ c$. The modified time of subject $l$ is

$$
\tilde X_l = \begin{cases} \displaystyle\sum_{m=1}^{n} |X_m| & \text{if subject } l \text{ has a competing event},\\ X_l & \text{otherwise,} \end{cases}
$$

so censored subjects and cause-$c$ failures keep their observed times. Replacing competing-event times by $\sum_m |X_m|$ is a finite encoding of the risk set that keeps subjects with a competing event (they are then at risk at every observed time), not a formula from the papers below.

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509.
- X. Zhang, M.-J. Zhang and J. P. Fine, "A proportional hazards regression model for the subdistribution with right-censored and left-truncated competing risks data", Stat. Med. 30 (2011), 1933–1951 (PMC3408877), Section 3, the unnumbered complete-data partial-likelihood display before eq. (2) and the sentence following it defining the risk set $R_i$.
