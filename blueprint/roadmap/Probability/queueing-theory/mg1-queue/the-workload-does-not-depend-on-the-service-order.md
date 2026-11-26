# The workload does not depend on the service order

Consider a single-server queue with given arrival times and given service requirements, served by a work-conserving discipline: the server works at rate $1$ whenever work is present, and no work is created or lost. Let $V(t)$ be the amount of work in the system at time $t$, the sum of the remaining service requirements. Then $V$ is the same function of time for every such discipline, preemptive or not: it jumps by the service requirement of each arriving customer and decreases at rate $1$ while positive, both determined by the arrival data alone. In particular the busy periods, and the mean amount of work in a stationary queue, do not depend on the order of service.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 9.4 (the observation that the amount of work in the system does not depend on the order in which customers are served).
