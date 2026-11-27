# Pollaczek–Khinchine formula for the queue length

In the M/G/1 queue customers arrive according to a Poisson process of rate $\lambda > 0$ and are served one at a time, first come first served, by a single server; the service times are i.i.d. copies of a nonnegative random variable $B$ with $E[B] > 0$, independent of the arrival process, with Laplace–Stieltjes transform $\tilde B(s) = E[e^{-sB}]$, and the occupation rate is $\rho = \lambda E[B] < 1$. Let $d_n$ be the limiting probability that a departing customer leaves $n$ customers behind. Its generating function $P_{L^d}(z) = \sum_n d_n z^n$ is

$$
P_{L^d}(z) = \frac{(1 - \rho)\,\tilde B(\lambda - \lambda z)\,(1 - z)}{\tilde B(\lambda - \lambda z) - z}, \qquad |z| < 1 .
$$

Since customers arrive and leave one at a time, arriving customers, departing customers and outside observers all see the same limiting distribution of the number in the system, so this is also the generating function of the time-stationary number in the system. The formula comes from the embedded Markov chain $L^d_{k+1} = L^d_k - \mathbf 1\{L^d_k > 0\} + A_{k+1}$ at departure epochs, where $A_{k+1}$, the number of arrivals during a service time, has generating function $\tilde B(\lambda - \lambda z)$.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)

## Proof depends on

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): the arrival distribution is the time-stationary one.

## Expansion

This page becomes ready once these prerequisites are stated:

- the embedded Markov chain of the M/G/1 queue at departure epochs and its positive recurrence exactly when $\rho < 1$, with its limiting distribution $(d_n)$;
- the number of Poisson arrivals during an independent service time, with generating function $\tilde B(\lambda - \lambda z)$;
- equality of the distributions seen at arrivals and at departures for systems in which customers arrive and leave one by one.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.1 (the three limiting distributions coincide) and Section 7.2 (the embedded chain, equations (7.2)–(7.5), and formula (7.6)).
