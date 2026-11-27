# Peterson's filter lock and the single-register impossibility

Peterson's $n$-process filter lock uses atomic registers $\mathit{level}[i] \in \{0, \dots, n-1\}$ and $\mathit{victim}[k]$ for waiting rooms $k = 1, \dots, n - 1$: to enter room $k$, process $i$ writes $\mathit{level}[i] := k$ and then $\mathit{victim}[k] := i$, and waits while some other process $j$ has $\mathit{level}[j] \ge k$ and $\mathit{victim}[k] = i$, each room's condition being evaluated by individual reads; after room $n - 1$ it enters the critical section, and on leaving it resets $\mathit{level}[i] := 0$. For $k = 1, \dots, n - 1$, at any time at most $n - k$ processes have completed the waiting loop of room $k$ in their current attempt, so at most one process is in the critical section (mutual exclusion), and the lock is deadlock-free. (A process writes its level before waiting in that room, so the number of processes whose register reads at least $k$ is not bounded by $n - k$.) By contrast, no deadlock-free mutual exclusion algorithm for $n \ge 2$ processes uses a single shared read/write register.

## Proof sketch

By induction on $k$: of the at most $n - k + 1$ processes that have completed room $k - 1$, the last one to write $\mathit{victim}[k]$ cannot complete room $k$ while another of them is at level $k$ or above, so each room filters out at least one process. For one register, a covering argument lets a process enter the critical section while another's pending write erases all trace of it.

## Depends on

- [Mutual exclusion in Peterson's algorithm](../../peterson-s-mutual-exclusion-algorithm/mutual-exclusion.md)
- [The asynchronous shared-memory model](../the-asynchronous-shared-memory-model.md)
- [Progress conditions for concurrent implementations](../progress-conditions-for-concurrent.md)

## Sources

- Gary L. Peterson, "Myths About the Mutual Exclusion Problem", Information Processing Letters, 1981.
- James E. Burns and Nancy A. Lynch, "Bounds on Shared Memory for Mutual Exclusion", Information and Computation, 1993.
