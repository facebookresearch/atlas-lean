# Renewal-reward theorem

Let a positive recurrent [renewal process](renewal-processes.md) earn a reward $R_j$ during its $j$-th cycle, of length $X_j$, where the pairs $(X_j, R_j)$, $j \ge 1$, are i.i.d. with $E|R_1| < \infty$, and let $R(t)$ be the total reward earned by time $t$, made of the rewards of the cycles completed by $t$ and a partial reward $l(t)$ from the current cycle that is bounded in absolute value by the reward $|R_{N(t)+1}|$ of that cycle. Then

$$
\lim_{t \to \infty} \frac{R(t)}{t} = \frac{E[R_1]}{E[X_1]} = \lambda E[R_1] \quad \text{almost surely}.
$$

The long-run reward rate is the mean reward per cycle divided by the mean cycle length; for example, the long-run fraction of time a component is up is the mean up time per cycle over the mean cycle length.

## Depends on

- [Renewal processes](renewal-processes.md)

## Proof depends on

- [Elementary renewal theorem](elementary-renewal-theorem.md): the almost-sure limit $N(t)/t \to \lambda$.
- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Sources

- K. Sigman, *Some basic renewal theory: the renewal reward theorem*, lecture notes, IEOR 4106, Columbia University, 2018, <http://www.columbia.edu/~ks20/4106-18-Fall/Notes-RRT.pdf>, Section 1.2, Theorem 1.2 (renewal reward theorem), equation (4), with its proof. The source also states the limit of $E[R(t)]/t$, equation (5), which this page omits.
