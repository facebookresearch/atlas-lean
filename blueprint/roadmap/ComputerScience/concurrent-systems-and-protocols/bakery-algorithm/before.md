# Lamport's order on (ticket, name) pairs

For $N$ processes named $0, \dots, N - 1$, natural numbers $n$, $m$ and processes $i$, $k$: $(n, i) < (m, k)$ when $n < m$, or $n = m$ and $i < k$ (Lamport 1974, p. 454).

## Related topics

- [Ticket order of the two-process bakery algorithm](../two-process-bakery-algorithm/before.md): the order in the separate model of the two-process case.

## Sources

- L. Lamport, *A New Solution of Dijkstra's Concurrent Programming Problem*, Communications of the ACM 17(8), August 1974, 453–455: p. 454.
