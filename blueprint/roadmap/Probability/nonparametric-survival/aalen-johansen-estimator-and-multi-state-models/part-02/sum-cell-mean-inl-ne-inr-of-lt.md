# Observed event mass differs from the at-risk mass before the horizon

Let $k$ and $r$ be natural numbers. A subject is a point $w = ((T, J), C)$ of $\mathcal{W} = (\{0, \dots, k-1\} \times \{0, \dots, r-1\}) \times \{0, \dots, k-1\}$: an event-time grid index $T$, a cause $J$ and a censoring grid index $C$.

Let $\mu$ be a finite measure on $\mathcal{W}$. For a grid index $l$ and a cause $c$, the observed cause-$c$ event mass and the observed at-risk mass are

$$e_\mu(l, c) = \mu\{(T, J, C) : \min(T, C) = l,\ T \le C,\ J = c\}, \qquad y_\mu(l) = \mu\{(T, J, C) : l \le \min(T, C)\},$$

as real numbers; they are the coordinates of the [mean cell vector](../part-01/cell-mean.md) of $\mu$.

For all grid indices $l < m$ with $y_\mu(m) \ne 0$,

$$\sum_{c=0}^{r-1} e_\mu(l, c) \ne y_\mu(l).$$
