# Steps of Peterson's algorithm

In Peterson's algorithm for two processes, process $i$ raises its flag, sets $\mathrm{turn}$ to the other process, waits while the other process's flag is raised and $\mathrm{turn}$ favors the other process, enters its critical section, and on exit lowers its flag; each assignment and each test of the waiting condition is one atomic step.
