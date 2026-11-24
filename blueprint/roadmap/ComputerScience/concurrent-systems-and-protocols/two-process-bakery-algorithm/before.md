# Ticket order of the two-process bakery algorithm

In a state of the two-process bakery algorithm, process $i$ comes before process $j$ when the
ticket of $i$ is smaller than the ticket of $j$, or the tickets are equal, $i = p_0$ and $j = p_1$:
the lexicographic order on (ticket, process) pairs with $p_0 < p_1$. It is the two-process version of
[Lamport's order on (ticket, name) pairs](../bakery-algorithm/before.md).
