# Poisson arrivals during an independent service time

Let $A$ be the number of points of a [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md) of rate $\lambda$ in an interval of length $B$, where $B \ge 0$ is a random variable independent of the process with distribution function $F_B$ and Laplace–Stieltjes transform $\tilde B(s) = E[e^{-sB}]$. Then

$$
P(A = n) = \int_0^\infty \frac{(\lambda t)^n}{n!} e^{-\lambda t}\, dF_B(t), \qquad E[z^A] = \tilde B(\lambda - \lambda z) \quad (|z| \le 1),
$$

and $E[A] = \lambda E[B]$. In the M/G/1 queue these are the transition probabilities $\alpha_n$ of the embedded chain at departure epochs, the number of arrivals during one service.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.2, equation (7.2) and the generating function of the number of arrivals during a service time used in the derivation of (7.5).
