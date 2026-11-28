# Starvation under wait-die without its liveness assumptions

Under the wait-die scheme, two assumptions of the no-starvation theorem are needed: that a transaction holding all the locks it requests
commits, and that a rolled-back transaction restarts with its original timestamp.

1. **A holder that never finishes.** If an older transaction $T_o$ holds all the locks it requests and keeps one of them forever, never committing or
   aborting, then a younger transaction $T_y$ that requests that item is rolled back on every attempt and never commits. No lock-manager action granting
   the item is ever enabled, so weak fairness of the lock manager holds vacuously. The hypothesis that a transaction holding all the locks it requests
   commits excludes this execution.
2. **No timestamp retention.** If a rolled-back transaction restarts with a fresh, larger timestamp, a transaction $T$ can starve: in an execution in
   which, at each attempt of $T$, the item $T$ first requests is held by a transaction older than $T$'s current timestamp, $T$ is rolled back on every
   attempt and never commits. Such an execution needs an unbounded supply of transactions, each started before $T$'s latest restart.

## Proof

In both executions every step follows wait-die: a requester younger than the holder is rolled back, and an older one waits. In (1) the holder never
releases its lock. In (2) the assumed arrivals supply, at each attempt, a holder older than $T$'s current timestamp; since $T$'s timestamp grows with
every restart, $T$ never becomes older than those holders.

## Expansion

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Weak and strong fairness on omega-executions.

## Depends on

- [No starvation under wait-die/wound-wait with retained timestamps (optional liveness)](no-starvation-under-wait-die-wound-wait-with-retained-timest.md)

## Sources

- P. A. Bernstein, V. Hadzilacos and N. Goodman, *Concurrency Control and Recovery in Database Systems*, Addison-Wesley, 1987 (authors' free edition), Section 3.11 (pp. 84–86): livelock under priority-based prevention, wait-die and wound-wait, and the two restrictions that only finitely many timestamps precede any given one and that a restarted transaction keeps its old timestamp, without which it might never become the oldest; the bibliographic notes (p. 104) credit timestamp-based prevention to Rosenkrantz, Stearns and Lewis (1978). <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/05/chapter3.pdf>
