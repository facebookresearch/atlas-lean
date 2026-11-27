# The working set of a process

Consider a process whose execution is measured in process time and which references pages at instants of that time. For a time $t$ and a *working set parameter* $\tau \ge 0$, the *working set* $W(t, \tau)$ is the set of pages referenced by the process during the process-time interval $(t - \tau, t]$, and the *working set size* $\omega(t, \tau)$ is the number of pages in $W(t, \tau)$. Denning writes the open interval $(t - \tau, t)$; the half-open interval used here makes the interval decompositions of working sets exact, since a reference at a dividing instant then falls into exactly one of the two windows. The working set is the set of the most recently used pages; a working-set memory policy keeps exactly $W(t, \tau)$ in main memory, removing a page the moment it leaves the working set.

## Sources

- P. J. Denning, "The working set model for program behavior", *Communications of the ACM* 11(5), 1968, Section 3 (the definition of $W(t, \tau)$ and Figure 2, and equation (1) for $\omega(t, \tau)$).
