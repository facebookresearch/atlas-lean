# Stationary law of the M/M/1 queue-length process

Let $\lambda \ge 0$ and $\mu > 0$, and let $X$ be the continuous-time Markov chain on $\{0, 1, 2, \dots\}$ with jump rates $q(n, n+1) = \lambda$ and $q(n, n-1) = \mu$ for $n \ge 1$, constructed from its embedded jump chain and exponential holding times. Its total jump rates are bounded by $\lambda + \mu$, so it is non-explosive.

- If $0 < \lambda < \mu$, the chain is irreducible and positive recurrent; the geometric law $\pi_n = (1-\rho)\rho^n$, $\rho = \lambda/\mu$, is its unique stationary distribution and its limiting distribution, and the time-average queue length is $\sum_n n\pi_n = \rho/(1-\rho)$ almost surely.
- If $\lambda \ge \mu > 0$, the chain is irreducible and not positive recurrent, and the long-run fraction of time spent in each state is $0$.
- If $\lambda = 0$, the state $0$ has total jump rate $0$ and is never left (its holding time is infinite), every other state moves down at rate $\mu$, and $\delta_0$ is the unique stationary distribution and the limit from every initial state.

Statements about the waiting times of individual customers use the customer-level model and Little's law and are separate.

## Proof depends on

- [Balance distribution of the M/M/1 queue](mm1-balance-distribution.md): the balance relations have a probability solution exactly when $\lambda < \mu$, namely the geometric law.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Bounded jump rates imply non-explosion of a continuous-time Markov chain on a countable set.
- An irreducible non-explosive continuous-time Markov chain is positive recurrent if and only if its balance equations have a probability solution, which is then the unique stationary and limiting distribution.
- Time averages of a positive recurrent chain converge almost surely to stationary means, including for nonnegative unbounded functions such as $f(n) = n$.

## Sources

- K. Sigman, *Continuous-time Markov chains*, lecture notes, Columbia University, 2009, <http://www.columbia.edu/~ks20/stochastic-I/stochastic-I-CTMC.pdf>, §1.6, §1.8 Proposition 1.1, §1.10 Proposition 1.2, §1.12 Theorem 1.1, and the M/M/1 example (22)–(25)
- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §4.2–4.3
