# Cause-specific ratio times at-risk mass equals the event mass at the mean cell vector

Let $k$ and $r$ be natural numbers. A subject is a point $w = ((T, J), C)$ of $\mathcal{W} = (\{0, \dots, k-1\} \times \{0, \dots, r-1\}) \times \{0, \dots, k-1\}$: an event-time grid index $T$, a cause $J$ and a censoring grid index $C$.

Let $\mu$ be a finite measure on $\mathcal{W}$. For a grid index $l$ and a cause $c$, the observed cause-$c$ event mass and the observed at-risk mass are

$$e_\mu(l, c) = \mu\{(T, J, C) : \min(T, C) = l,\ T \le C,\ J = c\}, \qquad y_\mu(l) = \mu\{(T, J, C) : l \le \min(T, C)\},$$

as real numbers.

These are the coordinates of the [mean cell vector](../part-01/cell-mean.md) of $\mu$ at the event cell $(l, c)$ and at the at-risk cell $l$. The cause-$c$ ratio of the mean cell vector at $l$ is $\lambda_{l,c} = e_\mu(l, c) / y_\mu(l)$, with real division, $x/0 = 0$.

For every grid index $l$ and every cause $c$,

$$\lambda_{l,c}\, y_\mu(l) = e_\mu(l, c),$$

including the case $y_\mu(l) = 0$.
