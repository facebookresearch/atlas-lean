# Pollaczek–Khinchine formula for the waiting time

In the M/G/1 queue customers arrive according to a Poisson process of rate $\lambda > 0$ and are served one at a time, first come first served, by a single server; the service times are i.i.d. copies of a nonnegative random variable $B$ with $E[B] > 0$, independent of the arrival process, with Laplace–Stieltjes transform $\tilde B(s) = E[e^{-sB}]$, and the occupation rate is $\rho = \lambda E[B] < 1$. The waiting time $W$ of a customer arriving in the stationary regime, the time from its arrival until its service starts, has Laplace–Stieltjes transform

$$
\tilde W(s) = E[e^{-sW}] = \frac{(1 - \rho)\, s}{\lambda \tilde B(s) + s - \lambda} = \frac{1 - \rho}{1 - \rho \tilde R(s)}, \qquad s > 0,
$$

where $\tilde R(s) = (1 - \tilde B(s))/(sE[B])$ is the transform of the residual service time $R$, with density $P(B > t)/E[B]$ on $t \ge 0$. So $W$ is distributed as a geometric sum $R_1 + \dots + R_K$ of i.i.d. copies of $R$ with $P(K = k) = (1 - \rho)\rho^k$. It follows from the [Pollaczek–Khinchine formula for the sojourn time](pollaczek-khinchine-formula-for-the-sojourn-time.md) because $S = W + B$ with $W$ and the customer's own service time $B$ independent. Differentiating at $s = 0$ recovers the [Pollaczek–Khinchine mean waiting time](../lindley-recursion/pollaczek-khinchine-mean-value-formula.md) $E[W] = \rho E[R]/(1 - \rho)$.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)
- [Pollaczek–Khinchine formula for the sojourn time](pollaczek-khinchine-formula-for-the-sojourn-time.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- independence of the waiting time of a customer and its own service time under first-come first-served service, so that $\tilde S = \tilde W \tilde B$;
- the transform of the equilibrium residual time $R$, obtained by partial integration.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.4, equations (7.8)–(7.9), and Section 7.8, equation (7.17).
