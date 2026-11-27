# Operational quantities of an observation interval

Observe a system for an interval of length $T > 0$ and record the number $A$ of request arrivals and the number $C$ of request completions. The *arrival rate* is $\lambda = A/T$ and the *throughput* is $X = C/T$. For a single resource, let $B$ be the time it was observed busy; its *utilization* is $U = B/T$ and, when $C > 0$, its *average service requirement* per request is $S = B/C$. If the system contains resources $k = 1, \dots, K$, let $C_k$ be the number of completions at resource $k$; the *visit count* of resource $k$ is $V_k = C_k/C$, the average number of visits a system-level request makes to it, and its *service demand* is $D_k = V_k S_k = B_k/C$. Let $W$ be the accumulated time in the system during the interval, the area between the arrival and completion counting functions in request-seconds; the *average number in the system* is $N = W/T$ and the *average residence time* per request is $R = W/C$.

## Sources

- E. D. Lazowska, J. Zahorjan, G. S. Graham and K. C. Sevcik, *Quantitative System Performance: Computer System Analysis Using Queueing Network Models*, Prentice-Hall, 1984, online edition <https://homes.cs.washington.edu/~lazowska/qsp/>, Chapter 3, Sections 3.2 (basic quantities), 3.3 (the accumulated time in system, $N$ and $R$) and 3.4 (visit counts and service demands).
