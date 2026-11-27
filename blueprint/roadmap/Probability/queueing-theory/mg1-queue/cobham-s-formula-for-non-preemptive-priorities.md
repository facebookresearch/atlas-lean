# Cobham's formula for non-preemptive priorities

Consider a single-server queue with $r$ classes of customers, class $i$ arriving according to a Poisson process of rate $\lambda_i$, the classes independent, with i.i.d. service times distributed as $B_i$, $E[B_i^2] < \infty$, and residual service time $R_i$ with $E[R_i] = E[B_i^2]/(2E[B_i])$. Put $\rho_i = \lambda_i E[B_i]$ and $\sigma_i = \rho_1 + \dots + \rho_i$ ($\sigma_0 = 0$), and assume $\sigma_r < 1$. Class $1$ has the highest priority; within a class customers are served first come first served. Under the non-preemptive priority rule, in which a customer in service is never interrupted and the server always takes next a waiting customer of the highest class present, the stationary mean waiting time of a class-$i$ customer is

$$
E[W_i] = \frac{\sum_{j=1}^{r} \rho_j E[R_j]}{(1 - \sigma_i)(1 - \sigma_{i-1})}, \qquad i = 1, \dots, r,
$$

and its mean sojourn time is $E[S_i] = E[W_i] + E[B_i]$. For $i = 1$ the formula follows from $E[W_1] = E[L^q_1] E[B_1] + \sum_j \rho_j E[R_j]$ and Little's law $E[L^q_1] = \lambda_1 E[W_1]$; for lower classes the waiting time also contains the higher-priority work arriving while the customer waits.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)
- [Little's law](../littles-law/littles-law.md)

## Proof depends on

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): for each class, an arriving customer finds a class-$j$ customer in service with probability $\rho_j$ and then waits for its residual service time.

## Expansion

This page becomes ready once these prerequisites are stated:

- existence of the stationary regime of the multiclass queue when $\sigma_r < 1$;
- the mean of the higher-priority work arriving during a waiting time, as in the derivation of equation (9.2) of the source.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 9.1, equations (9.1)–(9.4).
