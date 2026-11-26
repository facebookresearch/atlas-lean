# Observed at-risk mass is non-increasing in the grid index

Let $k$ and $r$ be natural numbers. A subject is a point $w = ((T, J), C)$ of $\mathcal{W} = (\{0, \dots, k-1\} \times \{0, \dots, r-1\}) \times \{0, \dots, k-1\}$: an event-time grid index $T$, a cause $J$ and a censoring grid index $C$.

Let $\mu$ be a finite measure on $\mathcal{W}$. For a grid index $j$, the observed at-risk mass is

$$y_\mu(j) = \mu\{(T, J, C) : j \le \min(T, C)\},$$

as a real number.

For all grid indices $i \le j$,

$$y_\mu(j) \le y_\mu(i).$$
