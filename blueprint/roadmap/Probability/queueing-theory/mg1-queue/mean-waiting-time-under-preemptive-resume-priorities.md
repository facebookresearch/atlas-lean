# Mean waiting and sojourn times under preemptive-resume priorities

Consider a single-server queue with $r$ classes of customers, class $i$ arriving according to a Poisson process of rate $\lambda_i$, the classes independent, with i.i.d. service times distributed as $B_i$, $E[B_i^2] < \infty$, and residual service time $R_i$ with $E[R_i] = E[B_i^2]/(2E[B_i])$. Put $\rho_i = \lambda_i E[B_i]$ and $\sigma_i = \rho_1 + \dots + \rho_i$ ($\sigma_0 = 0$), and assume $\sigma_r < 1$. Class $1$ has the highest priority; within a class customers are served first come first served. Under the preemptive-resume priority rule, in which an arriving customer interrupts the service of any lower-class customer, whose service is later resumed with no work lost, the stationary mean waiting time and mean sojourn time of a class-$i$ customer are

$$
E[W_i] = \frac{\sum_{j=1}^{i} \rho_j E[R_j]}{(1 - \sigma_i)(1 - \sigma_{i-1})}, \qquad
E[S_i] = E[W_i] + \frac{E[B_i]}{1 - \sigma_{i-1}}, \qquad i = 1, \dots, r .
$$

Lower classes are invisible to a class-$i$ customer, and the work in the system does not depend on the order of service, so its waiting time is as in [Cobham's formula](cobham-s-formula-for-non-preemptive-priorities.md) with $\lambda_{i+1} = \dots = \lambda_r = 0$; its service is stretched by the higher-priority work arriving during it, to a mean of $E[B_i]/(1 - \sigma_{i-1})$.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)
- [Cobham's formula for non-preemptive priorities](cobham-s-formula-for-non-preemptive-priorities.md)

## Proof depends on

- [The workload does not depend on the service order](the-workload-does-not-depend-on-the-service-order.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- the mean length of a service time extended by all higher-priority work arriving during it, a busy period started by that service.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 9.2, the derivation and formula (9.5).
