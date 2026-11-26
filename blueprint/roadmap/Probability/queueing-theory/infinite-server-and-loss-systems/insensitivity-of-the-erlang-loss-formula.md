# Insensitivity of the Erlang loss formula

In the M/G/$c$/$c$ loss system customers arrive according to a Poisson process of rate $\lambda > 0$; there are $c \ge 1$ servers, an arriving customer who finds a free server starts service immediately and one who finds all servers busy is lost; service times are i.i.d. copies of a nonnegative random variable $B$ with $E[B] < \infty$, independent of the arrivals. With $\rho = \lambda E[B]$, the limiting probability of $n$ customers in the system is

$$
p_n = \frac{\rho^n / n!}{\sum_{k=0}^{c} \rho^k / k!}, \qquad n = 0, 1, \dots, c,
$$

whatever the distribution of $B$. In particular the fraction of customers lost is given by [Erlang's loss formula](../markovian-queues/erlang-loss-formula.md) $B(c, \rho) = p_c$, which depends on the service-time distribution only through its mean, and the mean number of busy servers is $\rho(1 - B(c, \rho))$. For exponential service times this is the [stationary law of the Erlang loss system](../markovian-queues/stationary-law-of-the-erlang-loss-system.md).

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)
- [Erlang's loss formula](../markovian-queues/erlang-loss-formula.md)

## Proof depends on

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): to read $p_c$ as the fraction of customers lost.

## Expansion

This page becomes ready once this prerequisite is stated and the source of the general case, which the cited notes take from the literature, is checked:

- a Markovian description of the loss system with general service times, for example by the residual or elapsed service times of the customers in service, and its stationary distribution.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 11.2, Example 11.2.1 (the exponential case) and formula (11.2) for general service times.
