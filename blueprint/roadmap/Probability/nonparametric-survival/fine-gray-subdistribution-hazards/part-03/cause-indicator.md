# Cause-specific event indicator

Let $\iota$ be a set of causes, $n \in \mathbb{N}$, $c \in \iota$ a cause of interest and statuses $\varepsilon_1, \dots, \varepsilon_n$, where $\varepsilon_l = \mathrm{none}$ means subject $l$ is censored and $\varepsilon_l = \mathrm{some}\ c'$ means subject $l$ fails from cause $c' \in \iota$.

The cause-$c$ event indicator of subject $i \in \{1, \dots, n\}$ is the Boolean

$$
\delta_i = \begin{cases} \mathrm{true} & \text{if } \varepsilon_i = \mathrm{some}\ c,\\ \mathrm{false} & \text{otherwise,} \end{cases}
$$

so $\delta_i$ is false both for a censored subject and for a subject failing from a cause other than $c$.

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509, Section 3.
