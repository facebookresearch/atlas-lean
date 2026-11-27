# The conservation law for mean waiting times

Consider a single-server queue with $r$ types of customers, type $i$ arriving with rate $\lambda_i$ (the arrival streams need not be Poisson), with mean service time $E[B_i]$ and mean residual service time $E[R_i]$, and $\sum_i \rho_i < 1$ where $\rho_i = \lambda_i E[B_i]$. Let $P$ range over the service disciplines that are work-conserving, never interrupt a service, and choose the customers to enter service in an order independent of their service times, such as first come first served, random order or a non-preemptive priority rule. Then

$$
\sum_{i=1}^{r} \rho_i\, E[W_i(P)]
$$

does not depend on $P$, where $E[W_i(P)]$ is the stationary mean waiting time of type $i$ under $P$. An improvement of one type's mean waiting time by a change of discipline must therefore be paid for by another type. The proof writes the mean work in the system as $\sum_i E[L^q_i(P)] E[B_i] + \sum_i \rho_i E[R_i]$, notes that the work in the system does not depend on the discipline, and applies Little's law $E[L^q_i] = \lambda_i E[W_i(P)]$.

## Depends on

- [Little's law](../littles-law/littles-law.md)

## Proof depends on

- [The workload does not depend on the service order](the-workload-does-not-depend-on-the-service-order.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- existence of the stationary regime under each discipline and of the stationary mean work in the system;
- the time-average work at the server, $\sum_i \rho_i E[R_i]$, from the long-run fraction $\rho_i$ of time the server spends on type-$i$ customers and the residual-life argument for the service in progress.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 9.4, equation (9.8) and the conservation law, with Example 9.4.1.
