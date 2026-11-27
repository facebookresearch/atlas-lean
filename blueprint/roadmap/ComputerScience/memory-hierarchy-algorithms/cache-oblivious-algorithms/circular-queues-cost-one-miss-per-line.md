# Circular queues cost one miss per line

In the [ideal-cache model](the-ideal-cache-model.md) with lines of $L$ words, performing $r$ insert and remove operations on a circular queue causes $O(1 + r/L)$ cache misses, as long as two cache lines are available for the queue, one for the head and one for the tail. The bound is amortized: each end moves sequentially through the buffer, so it misses once per line it enters, plus at most one extra miss per traversal for the partial lines at the two ends of the buffer. The misses need not be spaced $L$ operations apart: with lines of $4$ words, a buffer at addresses $0$ to $8$ and a cold cache, two successive inserts at addresses $8$ and $0$ both miss. A buffer spanning at most two lines fits in the cache outright.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 4, Lemma 5 with its proof.
