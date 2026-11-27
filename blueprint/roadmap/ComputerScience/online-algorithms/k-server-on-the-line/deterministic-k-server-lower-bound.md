# No deterministic k-server algorithm beats ratio k

On every metric space with at least $k + 1$ points, no deterministic online $k$-server algorithm is $(c, b)$-competitive for any ratio $c < k$ and any additive constant $b$; more precisely, for every rational $p / q < k$ and every $b$ there is a request sequence on which the algorithm's cost exceeds $(p/q)\,\mathrm{OPT} + b$.

## Proof sketch

First normalize to a lazy algorithm, which moves only the server needed to cover an uncovered request; by the triangle inequality this never increases cost. On $k + 1$ fixed points, the adversary always requests the point not covered by the online servers, so the online algorithm pays at every request. Consider the $k$ offline algorithms that each keep a different point uncovered and move only when that point is requested; their total cost equals the online cost minus a bounded start-up term, so their average is a $1/k$ fraction of the online cost, and the cheapest offline algorithm is at least that good.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [Online request-serving problem and competitive ratio](../competitive-analysis/online-problem-and-competitive-ratio.md)

## Proof depends on

- [Matching distance between server configurations](matching-distance-between-configurations.md)

## Sources

- M. S. Manasse, L. A. McGeoch and D. D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2), 1990.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
