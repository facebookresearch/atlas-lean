# Waiting and sojourn times in the M/M/1 queue

In the first-come first-served M/M/1 queue with arrival rate $\lambda$ and service rate $\mu$, $0 < \lambda < \mu$, $\rho = \lambda/\mu$, a customer arriving in steady state has sojourn time $S$ exponential with rate $\mu - \lambda$ and waiting time $W$ with $P(W > t) = \rho e^{-(\mu - \lambda)t}$ for $t \ge 0$; so $E[S] = 1/(\mu - \lambda)$, $E[W] = \rho/(\mu - \lambda)$, and $W$ given $W > 0$ is exponential with rate $\mu - \lambda$. The number $L_a$ found on arrival has the geometric law $(1-\rho)\rho^n$ by PASTA, and by the memoryless property $S$ is the sum of $L_a + 1$ independent exponential service times.

## Proof depends on

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): the arrival-seen queue length is geometric.
- [Stationary law of the M/M/1 queue-length process](stationary-law-of-the-mm1-queue-length-process.md): the stationary queue-length law.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- If $N$ takes values in $\{1, 2, \dots\}$ with $P(N = k) = p(1 - p)^{k-1}$ for some $0 < p \le 1$ and is independent of i.i.d. exponential random variables of rate $\mu$, then their sum over $k \le N$ is exponential with rate $p\mu$.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §4.3 (formula (4.9)) and §4.4 (formulas (4.10)–(4.14))
