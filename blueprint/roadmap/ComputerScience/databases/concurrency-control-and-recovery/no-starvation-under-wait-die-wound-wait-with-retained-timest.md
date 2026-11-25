# No starvation under wait-die/wound-wait with retained timestamps (optional liveness)

This node collects the liveness assumptions under which the wait-die and wound-wait schemes prevent starvation, as
statements separate from their deadlock freedom.

## Expansion

A sound expansion has separate pages for:

1. **Schemes.** Transactions carry distinct timestamps, a smaller timestamp meaning older, and request exclusive
   locks. When $T_i$ requests a lock held by $T_j$: under wait-die, $T_i$ waits if it is older than $T_j$ and is
   rolled back otherwise; under wound-wait, $T_j$ is rolled back if $T_i$ is older and $T_i$ waits otherwise. A
   rolled-back transaction restarts with its original timestamp.
2. **Deadlock freedom.** Under wait-die every wait-for edge goes from an older to a younger transaction, and under
   wound-wait from a younger to an older one, so neither scheme reaches a snapshot with circular wait.
3. **No starvation,** under explicit assumptions: only finitely many transactions with smaller timestamps than any
   given one ever exist (for example, timestamps are issued from an increasing clock and arrivals are finite in
   every bounded interval); each run of a transaction issues finitely many lock requests with finitely many steps
   between them; a transaction that holds all the locks it requests commits; the only aborts are the rollbacks
   the scheme itself causes; and the lock manager grants a released lock to some waiting transaction. Then every
   transaction eventually commits.
4. **Insufficiency of weaker hypotheses,** with examples: weak fairness of lock-manager actions alone does
   not suffice, a transaction need not become the oldest before it commits, and a transaction that is aborted
   for an outside reason each time it holds its locks never commits.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Weak and strong fairness on omega-executions.

## Depends on

- [Wait-for relation](../../concurrent-systems-and-protocols/deadlock-and-circular-wait/waits-for.md)
- [Circular wait](../../concurrent-systems-and-protocols/deadlock-and-circular-wait/circular-wait.md)

## Sources

- A. Silberschatz, H. F. Korth and S. Sudarshan, *Database System Concepts*, 7th edition, Chapter 18 slide 18.23 (wait-die and wound-wait; a rolled-back transaction restarts with its original timestamp, so older transactions have precedence and starvation is avoided). <https://www.db-book.com/slides-dir/PDF-dir/ch18.pdf>
- ECS165A Chapter 17 Concurrency Control slides (UC Davis), slide 10 (wait-die and wound-wait by timestamp priority; restart with the original timestamp). <https://expolab.org/ecs165a-winter2020/lectures/chapter17.pdf>
