# Peterson's filter lock and the single-register impossibility

Peterson's $n$-process filter lock uses atomic registers $\mathit{level}[i] \in \{0, \dots, n-1\}$ and $\mathit{victim}[r]$ for $n - 1$ waiting rooms, with each room's condition evaluated by individual reads. At most $n - (r + 1)$ processes are simultaneously at or above level $r + 1$, so at most one process is in the critical section (mutual exclusion), and the lock is deadlock-free. By contrast, no deadlock-free mutual exclusion algorithm for $n \ge 2$ processes uses a single shared read/write register.

## Proof sketch

In each waiting room the last process to write the victim register is blocked while others remain, so each room filters out at least one process. For one register, a covering argument lets a process enter the critical section while another's pending write erases all trace of it.

## Depends on

- [Mutual exclusion in Peterson's algorithm](../../peterson-s-mutual-exclusion-algorithm/mutual-exclusion.md)
- [The asynchronous shared-memory model](../the-asynchronous-shared-memory-model.md)
- [Progress conditions for concurrent implementations](../progress-conditions-for-concurrent.md)

## Sources

- Gary L. Peterson, "Myths About the Mutual Exclusion Problem", Information Processing Letters, 1981.
- James E. Burns and Nancy A. Lynch, "Bounds on Shared Memory for Mutual Exclusion", Information and Computation, 1993.
