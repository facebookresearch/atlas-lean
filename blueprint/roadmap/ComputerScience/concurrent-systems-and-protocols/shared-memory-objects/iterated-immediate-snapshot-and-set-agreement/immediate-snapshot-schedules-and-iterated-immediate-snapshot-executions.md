# Immediate snapshot schedules and iterated immediate snapshot executions

For a finite set $U$ of participating processes, a one-shot *immediate snapshot schedule* is an ordered partition $(B_1, \dots, B_k)$ of $U$ into nonempty blocks; every process in block $B_j$ writes and then immediately obtains the view $B_1 \cup \dots \cup B_j$. An $R$-round *iterated immediate snapshot* (IIS) execution applies such a schedule in each round, each process writing its entire previous view; a deterministic IIS protocol maps the final full-information view of each process to an output.

## Depends on

- [Atomic snapshot objects](../atomic-snapshot-objects.md)
- [The asynchronous shared-memory model](../the-asynchronous-shared-memory-model.md)

## Sources

- Elizabeth Borowsky and Eli Gafni, "A Simple Algorithmically Reasoned Characterization of Wait-Free Computations", Proceedings of the Sixteenth Annual ACM Symposium on Principles of Distributed Computing (PODC), 1997.
- Elizabeth Borowsky and Eli Gafni, "Generalized FLP Impossibility Result for t-Resilient Asynchronous Computations", Proceedings of the Twenty-Fifth Annual ACM Symposium on Theory of Computing (STOC), 1993.
- Maurice Herlihy and Nir Shavit, "The Topological Structure of Asynchronous Computability", Journal of the ACM, 1999.
