# Circular queues cost one miss per line

In the [ideal-cache model](the-ideal-cache-model.md) with lines of $L$ words, performing $r$ insert and remove operations on a circular queue causes $O(1 + r/L)$ cache misses, as long as two cache lines are available for the queue: one line serves the head and one the tail, and after a line is read, the next $L - 1$ operations at that end cause no miss.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 4, Lemma 5 with its proof.
