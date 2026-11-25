# LRU simulates the ideal cache up to a factor of two

If an algorithm incurs $Q(n; Z, L)$ cache misses on an ideal cache of $Z$ words with lines of $L$ words and optimal replacement, then on a fully associative cache of $2Z$ words with lines of $L$ words and LRU replacement, both caches starting empty, it incurs at most $2Q(n; Z, L)$ misses. Consequently, cache-miss bounds that satisfy the regularity condition $Q(n; Z, L) = O(Q(n; 2Z, L))$ hold for LRU caches up to constant factors.

## Depends on

- [The ideal-cache model](the-ideal-cache-model.md)

## Proof depends on

- [Resource-augmented competitiveness of LRU](../../online-algorithms/competitive-paging/resource-augmented-competitiveness-of-lru.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th IEEE FOCS*, 1999
- D. D. Sleator and R. E. Tarjan, "Amortized efficiency of list update and paging rules", *Communications of the ACM* 28(2):202–208, 1985
