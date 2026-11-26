# Event of a cause-of-interest failure by time t in the proportional subdistribution hazards family

On the sample space $\mathbb{R}$ the failure time $T$ and the failure cause $J$ are

$$
T(\omega) = \begin{cases} \dfrac{\omega}{1-\omega} & \text{if } \omega < 1,\\ 1 & \text{if } \omega \ge 1, \end{cases} \qquad J(\omega) = \begin{cases} \mathrm{true} & \text{if } \omega < 1,\\ \mathrm{false} & \text{if } \omega \ge 1, \end{cases}
$$

where $J = \mathrm{true}$ is the cause of interest and $J = \mathrm{false}$ the competing cause.

For every $t > -1$,

$$
\{\omega \in \mathbb{R} : T(\omega) \le t,\ J(\omega) = \mathrm{true}\} = \left(-\infty, \frac{t}{1+t}\right].
$$

## Sources

- J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a competing risk", J. Amer. Statist. Assoc. 94 (1999), 496–509, Section 2.
