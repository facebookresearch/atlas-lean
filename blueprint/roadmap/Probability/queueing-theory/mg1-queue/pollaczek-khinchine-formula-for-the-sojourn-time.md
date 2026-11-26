# Pollaczek–Khinchine formula for the sojourn time

In the M/G/1 queue customers arrive according to a Poisson process of rate $\lambda > 0$ and are served one at a time, first come first served, by a single server; the service times are i.i.d. copies of a nonnegative random variable $B$ with $E[B] > 0$, independent of the arrival process, with Laplace–Stieltjes transform $\tilde B(s) = E[e^{-sB}]$, and the occupation rate is $\rho = \lambda E[B] < 1$. The sojourn time $S$ of a customer arriving in the stationary regime, the time from its arrival to its departure, has Laplace–Stieltjes transform

$$
\tilde S(s) = E[e^{-sS}] = \frac{(1 - \rho)\,\tilde B(s)\, s}{\lambda \tilde B(s) + s - \lambda}, \qquad s > 0 .
$$

Under first-come first-served service, the customers a departing customer leaves behind are exactly those that arrived during its sojourn, so the generating function of the departure queue length is $\tilde S(\lambda - \lambda z)$; the formula follows from the [Pollaczek–Khinchine formula for the queue length](pollaczek-khinchine-formula-for-the-queue-length.md) by the substitution $s = \lambda - \lambda z$. For exponential service times with rate $\mu$, $S$ is exponential with rate $\mu(1 - \rho)$.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)
- [Pollaczek–Khinchine formula for the queue length](pollaczek-khinchine-formula-for-the-queue-length.md)

## Proof depends on

- [Poisson arrivals during an independent service time](poisson-arrivals-during-an-independent-service-time.md): applied to the sojourn time $S$.

## Expansion

This page becomes ready once these prerequisites are stated:

- the identity between a transform given on $s \in (0, \lambda]$ by the substitution and its analytic continuation to all $s > 0$.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.3, formula (7.7) and Example 7.3.1.
