# The ABD emulation of an atomic register

In an [asynchronous message-passing system](../distributed-execution-models/asynchronous-message-passing-systems.md) of $n$ processes of which at most $f < n/2$ may crash, with a reliable point-to-point link between every pair of processes, every message between correct processes eventually delivered, and every correct process taking infinitely many steps, the algorithm of Attiya, Bar-Noy and Dolev implements a single-writer multi-reader atomic register: the writer tags each value with an increasing timestamp and waits for acknowledgements from a majority; a reader queries a majority, takes the value with the largest timestamp, writes it back to a majority, and returns it. The implementation is linearizable, and every operation invoked by a correct process terminates. The bound is tight: for $f \ge n/2$ no such emulation exists, by a partition argument.

## Depends on

- [Asynchronous message-passing systems](../distributed-execution-models/asynchronous-message-passing-systems.md)
- [Linearizability](../shared-memory-objects/linearizability.md)
- [Quorum system](../paxos-consensus/quorum-system.md)
- [An admissible pattern has at most $T$ faulty processes](../synchronous-consensus-with-crash-failures/card-faulty-le.md)

## Sources

- Original algorithm: H. Attiya, A. Bar-Noy and D. Dolev, "Sharing memory robustly in message-passing systems", *Journal of the ACM* 42(1):124–142, 1995. The formulation follows Aspnes, the sections on the Attiya–Bar-Noy–Dolev algorithm and its proof of linearizability.
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
