# The Erlang-C delay probability and the mean wait in the M/M/s queue

Let $s \ge 1$, $\lambda \ge 0$, $\mu > 0$ with $\rho = \lambda/(s\mu) < 1$, $a = \lambda/\mu$, and let $\pi$ be the balance distribution of the M/M/s queue. The stationary probability that all servers are busy is the Erlang-C value

$$
\Pi_W = \sum_{n \ge s} \pi_n = \frac{a^s/(s!(1-\rho))}{\sum_{k<s} a^k/k! + a^s/(s!(1-\rho))},
$$

and the stationary mean number waiting is $E[L_q] = \sum_{n \ge s}(n - s)\pi_n = \Pi_W\,\rho/(1-\rho)$. For $\lambda > 0$, in the M/M/s queue with Poisson arrivals and first-come first-served service, PASTA makes $\Pi_W$ the long-run fraction of arriving customers who must wait, and Little's law applied to the waiting line gives the mean wait $E[W] = E[L_q]/\lambda = \Pi_W/(s\mu - \lambda)$. The Halfin–Whitt limit of $\Pi_W$ as $s \to \infty$ with $\sqrt{s}(1-\rho)$ held fixed is a separate statement.

## Depends on

- [Balance distribution of the M/M/s queue](mms-balance-distribution.md): the balance distribution $\pi$.

## Proof depends on

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): identifies $\Pi_W$ with the fraction of arrivals that wait.
- [Little's law](../littles-law/littles-law.md): applied to the waiting line, with arrival rate $\lambda$ and the time-average number waiting.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Ergodic theorem for the positive-recurrent M/M/s queue-length chain: its long-run time averages equal the means under the balance distribution almost surely.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §5.1 (formula (5.1)) and §5.2 (formulas (5.2)–(5.3))
