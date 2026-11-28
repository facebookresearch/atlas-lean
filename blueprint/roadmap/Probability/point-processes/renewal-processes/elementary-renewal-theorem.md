# Elementary renewal theorem

For a positive recurrent [renewal process](renewal-processes.md) with rate $\lambda = 1/E[X_1]$,

$$
\lim_{t \to \infty} \frac{N(t)}{t} = \lambda \quad \text{almost surely}.
$$

**Proof.** $t_{N(t)} \le t < t_{N(t)+1}$ and $N(t) \to \infty$; dividing by $N(t)$, both $t_{N(t)}/N(t)$ and $t_{N(t)+1}/N(t)$ tend to $E[X_1]$ by the strong law of large numbers, and $t/N(t)$ is squeezed between them.

## Depends on

- [Renewal processes](renewal-processes.md)

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Sources

- K. Sigman, *Some basic renewal theory: the renewal reward theorem*, lecture notes, IEOR 4106, Columbia University, 2018, <http://www.columbia.edu/~ks20/4106-18-Fall/Notes-RRT.pdf>, Section 1.1, Theorem 1.1 (elementary renewal theorem), first part, with its proof. The source also covers the null recurrent case $\lambda = 0$ and the limit $E[N(t)]/t \to \lambda$, which this page omits.
