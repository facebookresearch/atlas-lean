# The k-server problem on a uniform metric is paging

On a uniform metric space (all distinct points at distance $1$) with $k$ servers, a server configuration is a cache of at most $k$ pages (the occupied points), a request to an uncovered point costs exactly $1$ for a lazy algorithm, and lazy $k$-server algorithms correspond to demand-paging algorithms with cache size $k$ with the same cost on every request sequence. Hence competitive ratios of paging and of $k$-server on uniform metrics coincide.

## Proof sketch

Moving a server from point $p$ to the request $r$ costs $1$ and corresponds to evicting $p$ and loading $r$. By lazy normalization it suffices to consider lazy algorithms on both sides.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Deterministic online paging algorithm](../competitive-paging/deterministic-online-paging-algorithm.md)

## Proof depends on

- [Lazy normalization of k-server algorithms](lazy-normalization-of-k-server-algorithms.md)

## Sources

- M. S. Manasse, L. A. McGeoch and D. D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2), 1990.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
