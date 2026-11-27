# Burke's output theorem

Consider the M/M/$c$ queue with arrival rate $\lambda > 0$, $c \ge 1$ servers each of exponential service rate $\mu$, and $\lambda < c\mu$, with its queue-length process in the stationary regime. Then:

1. the departure process is a Poisson process with the same rate $\lambda$ as the arrival process;
2. the departure process before any time $t$ is independent of the number of customers in the system at time $t$.

Statement 1 implies that the second queue of a tandem of exponential single-server queues fed by a Poisson process behaves as an M/M/1 queue, and statement 2 that the numbers of customers at the two queues at a given time are independent, which gives the product form of the tandem. Both statements follow from the reversibility of the stationary queue-length process: reversing time turns departures into arrivals.

## Depends on

- [Poisson process](../../point-processes/poisson-processes/is-poisson-process.md)
- [Balance distribution of the M/M/s queue](mms-balance-distribution.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- the queue-length process of the M/M/$c$ queue as a continuous-time Markov chain whose stationary law is the balance distribution, and its reversibility in the stationary regime (a birth–death chain satisfying detailed balance);
- the time reversal of a stationary reversible birth–death process, which maps the departure epochs of the original process to the arrival epochs of the reversed one.

## Sources

- O. J. Boxma, *Stochastic Performance Modelling*, lecture notes, Eindhoven University of Technology, January 5, 2017, <https://www.win.tue.nl/~iadan/2WB60/lecturenotes.pdf>, Section 7.4, Burke's output theorem (statements (i) and (ii)) and Remark 7.7 (the proof by reversibility).
