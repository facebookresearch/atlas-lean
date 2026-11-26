# Poisson occupancy of the M/G/∞ queue

In the M/G/$\infty$ queue customers arrive according to a Poisson process of rate $\lambda > 0$ and each is served immediately by one of infinitely many servers, the service times being i.i.d. copies of a nonnegative random variable $B$ with $E[B] < \infty$, independent of the arrivals. Let $\rho = \lambda E[B]$. The limiting distribution of the number $L$ of customers in the system is Poisson with mean $\rho$,

$$
p_n = e^{-\rho} \frac{\rho^n}{n!}, \qquad n = 0, 1, 2, \dots,
$$

whatever the distribution of $B$; the waiting time is $0$ and $E[L] = \rho$ by Little's law. For deterministic service times $b$, the number present at any time $t > b$ is the number of arrivals in $(t - b, t]$; for a discrete service-time distribution the arrival stream splits into independent Poisson streams with constant service times, and the general case follows by approximation.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)

## Proof depends on

- [Little's law](../littles-law/littles-law.md): $E[L] = \rho$.

## Expansion

This page becomes ready once these prerequisites are stated:

- thinning of a Poisson process into independent Poisson streams according to i.i.d. marks, here the service times;
- the number present at time $t$ in a system started empty is Poisson with mean $\lambda \int_0^t P(B > u)\, du$, which increases to $\rho$, and convergence of Poisson laws when their means converge.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 11.1, formula (11.1) and Examples 11.1.1–11.1.3.
