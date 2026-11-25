# Pollaczek–Khinchine mean waiting time

In the first-come first-served M/G/1 queue with Poisson arrivals of rate $\lambda > 0$ and i.i.d. nonnegative service times $B$, independent of the arrival process, with $E[B^2] < \infty$ and $\rho = \lambda E[B] < 1$, the stationary mean waiting time is $E[W] = \lambda E[B^2]/(2(1 - \rho))$. If $E[B] = 0$, then $B = 0$ almost surely and $W = 0$, in agreement with the formula. If $E[B] > 0$, the mean-value argument runs as follows: by PASTA an arrival finds the server busy with probability $\rho$, and then waits for the residual service time $R$ of the customer in service, with $E[R] = E[B^2]/(2E[B])$, plus the services of the $L_q$ customers waiting, so $E[W] = E[L_q]E[B] + \rho E[R]$; Little's law for the queue gives $E[L_q] = \lambda E[W]$, and since $E[W] < \infty$ in the stationary regime the term $\rho E[W]$ may be subtracted, giving $E[W] = \rho E[R]/(1 - \rho)$.

## Proof depends on

- [Poisson arrivals see time averages](../poisson-arrivals-see-time-averages.md): arrivals find the server busy with probability $\rho$.
- [Little's law](../littles-law/littles-law.md): Little's law for the waiting line.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Existence of the stationary regime of the M/G/1 queue for $\rho < 1$, finiteness of the stationary mean waiting time when $E[B^2] < \infty$, and ergodicity of its time and customer averages.
- Mean residual service time $E[B^2]/(2E[B])$ seen by Poisson arrivals, for $E[B] > 0$.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, §7.6 (formula (7.14)) and the residual-time formula (7.15)
