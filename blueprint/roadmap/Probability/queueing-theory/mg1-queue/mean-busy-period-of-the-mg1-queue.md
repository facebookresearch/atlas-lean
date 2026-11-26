# Mean busy period of the M/G/1 queue

In the M/G/1 queue customers arrive according to a Poisson process of rate $\lambda > 0$ and are served one at a time, first come first served, by a single server; the service times are i.i.d. copies of a nonnegative random variable $B$ with $E[B] > 0$, independent of the arrival process, with Laplace–Stieltjes transform $\tilde B(s) = E[e^{-sB}]$, and the occupation rate is $\rho = \lambda E[B] < 1$. A busy period is an interval during which the server works without interruption, started by an arrival to an empty system. Its length $BP$ has mean

$$
E[BP] = \frac{E[B]}{1 - \rho} .
$$

In the renewal argument, a cycle consists of a busy period followed by an idle period, which is exponential with mean $1/\lambda$ by the memoryless property of the arrival process, and the fraction of time the server works is $\rho = E[BP]/(E[BP] + 1/\lambda)$. For exponential service times with rate $\mu$ this is $(1/\mu)/(1 - \rho)$.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- the busy cycles of the M/G/1 queue form a renewal process, with i.i.d. busy and idle periods;
- the renewal-reward theorem, which identifies the long-run fraction of busy time $\rho$ with $E[BP]/(E[BP] + 1/\lambda)$.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 4.6.1 (the M/M/1 case) and Section 7.9, formula (7.18).
