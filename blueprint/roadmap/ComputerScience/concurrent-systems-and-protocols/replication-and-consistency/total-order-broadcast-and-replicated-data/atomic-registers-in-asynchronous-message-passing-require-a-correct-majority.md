# Atomic registers in asynchronous message passing require a correct majority

In asynchronous crash-prone message passing with $2 \le n \le 2t$, no deterministic protocol emulates a wait-free linearizable multi-writer read/write register over any value set with at least two elements; for $n > 2t$, quorum-based read/write emulations with read write-back are linearizable and wait-free. Hence a wait-free linearizable register emulation tolerating $t$ crashes exists if and only if $n \le 1$ or $n > 2t$.

## Proof sketch

Split processes into two groups of at most $t$ and delay all messages between them; each group must complete a write and a subsequent read alone, so a read in one group misses a completed write in the other, violating linearizability. With majorities, every read quorum intersects every write quorum.

## Depends on

- [The ABD emulation of an atomic register](../the-abd-emulation-of-an-atomic-register.md)
- [Linearizability](../../shared-memory-objects/linearizability.md)
- [Asynchronous message-passing systems](../../distributed-execution-models/asynchronous-message-passing-systems.md)

## Proof depends on

- [The CAP theorem](../the-cap-theorem.md)

## Sources

- Hagit Attiya, Amotz Bar-Noy and Danny Dolev, "Sharing Memory Robustly in Message-Passing Systems", Journal of the ACM, 1995.
- Nancy A. Lynch and Alexander A. Shvartsman, "Robust Emulation of Shared Memory Using Dynamic Quorum-Acknowledged Broadcasts", Proceedings of the 27th Annual International Symposium on Fault-Tolerant Computing (FTCS '97), 1997.
