# Program counter of a bakery process

The program counter of a process of the bakery algorithm for $N$ processes takes one of the following values:

- in the noncritical section;
- in the doorway, choosing, with a set $U$ of processes whose entries are still to be read and a running maximum $m \in \mathbb{N}$;
- about to write the ticket $1 + m$, for $m \in \mathbb{N}$;
- about to reset $\mathrm{choosing}$;
- at statement L2 or at statement L3 of the loop, with an index $j \in \mathbb{N}$;
- in the critical section.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
