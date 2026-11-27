# Borowsky–Gafni characterization of immediate snapshot views

An assignment of views $V_i \subseteq U$ to processes $i \in U$ arises from an immediate snapshot schedule if and only if (self-inclusion) $i \in V_i$, (containment) any two views are ordered by inclusion, and (immediacy) $i \in V_j$ implies $V_i \subseteq V_j$. The schedule is uniquely determined by the views, giving a bijection between ordered partitions of $U$ and immediate-snapshot view assignments.

## Proof sketch

Group processes by their view; containment orders the distinct views as a chain, and self-inclusion with immediacy shows that the processes with a given view are exactly the new elements of that view, which reconstructs the blocks.

## Depends on

- [Immediate snapshot schedules and iterated immediate snapshot executions](immediate-snapshot-schedules-and-iterated-immediate-snapshot-executions.md)

## Sources

- Elizabeth Borowsky and Eli Gafni, "A Simple Algorithmically Reasoned Characterization of Wait-Free Computations", Proceedings of the Sixteenth Annual ACM Symposium on Principles of Distributed Computing (PODC), 1997.
