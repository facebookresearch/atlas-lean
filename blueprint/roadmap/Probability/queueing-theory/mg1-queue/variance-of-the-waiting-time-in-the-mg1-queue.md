# Variance of the waiting time in the M/G/1 queue

In the M/G/1 queue customers arrive according to a Poisson process of rate $\lambda > 0$ and are served one at a time, first come first served, by a single server; the service times are i.i.d. copies of a nonnegative random variable $B$ with $E[B] > 0$, independent of the arrival process, with Laplace–Stieltjes transform $\tilde B(s) = E[e^{-sB}]$, and the occupation rate is $\rho = \lambda E[B] < 1$. Assume in addition $E[B^3] < \infty$, and let $R$ be the residual service time, with density $P(B > t)/E[B]$, so that $E[R] = E[B^2]/(2E[B])$ and $E[R^2] = E[B^3]/(3E[B])$. The stationary waiting time $W$ satisfies

$$
E[W^2] = 2(E[W])^2 + \frac{\rho E[R^2]}{1 - \rho}, \qquad
\operatorname{Var}(W) = \frac{\rho}{(1 - \rho)^2}\Bigl( \rho (E[R])^2 + (1 - \rho) E[R^2] \Bigr),
$$

with $E[W] = \rho E[R]/(1 - \rho)$. Both follow by differentiating the transform $\tilde W(s) = (1 - \rho)/(1 - \rho \tilde R(s))$ twice at $s = 0$.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)
- [Pollaczek–Khinchine formula for the waiting time](pollaczek-khinchine-formula-for-the-waiting-time.md)

## Expansion

This page becomes ready once this prerequisite is stated:

- moments of a nonnegative random variable as derivatives of its Laplace–Stieltjes transform at $0$, when the moments are finite.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.8 (equation (7.17) and the second moment and variance of $W$ derived from it).
