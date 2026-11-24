# Mutual exclusion in Peterson's algorithm

In Peterson's algorithm for two processes, process $i$ raises its flag, sets $\mathrm{turn}$ to the other process, waits while the other process's flag is raised and $\mathrm{turn}$ favors the other process, enters its critical section, and on exit lowers its flag; each assignment and each test of the waiting condition is one atomic step. In no state reachable from an initial state (both processes idle, both flags down, arbitrary $\mathrm{turn}$) are both processes in their critical sections.
