# LIFO paging is not competitive

Let *last-in first-out* (LIFO) paging evict, on a miss with a full cache of $k$ pages, the page most recently brought into the cache. For $k = 1$ LIFO coincides with FIFO and is $(1, 0)$-competitive. For every $k \ge 2$ and every page universe with at least $k + 1$ distinct pages, LIFO is not $(c, b)$-competitive for any $c, b$: after $k - 1$ distinct warm-up requests, alternating requests to two further pages make LIFO fault at every request, while an offline cache of size $k$ faults only $k + 1$ times in total.

## Proof sketch

After the warm-up, the cache holds the $k - 1$ warm-up pages and the last loaded page; each request to the other alternating page evicts the most recently loaded page, which is exactly the next page requested. The offline algorithm keeps both alternating pages after its first two misses.

## Depends on

- [Deterministic online paging algorithm](../competitive-paging/deterministic-online-paging-algorithm.md)
- [Legal cache](../competitive-paging/legal-cache.md)
- [Online request-serving problem and competitive ratio](../competitive-analysis/online-problem-and-competitive-ratio.md)

## Proof depends on

- [FIFO is $k$-competitive](../competitive-paging/fifo-misses-le.md)

## Sources

- D. D. Sleator and R. E. Tarjan, "Amortized Efficiency of List Update and Paging Rules", Communications of the ACM 28(2), 1985.
