# The deterministic k-server conjecture

The *$k$-server conjecture* (Manasse, McGeoch and Sleator 1990) asserts that for every metric space with at least $k+1$ points there is a deterministic online $k$-server algorithm that is $k$-competitive, i.e. whose cost on every request sequence is at most $k$ times the offline optimum plus an additive constant depending only on the metric and the initial configuration. The value $k$ is a lower bound for every such metric, so the conjecture states that deterministic $k$-server is exactly $k$-competitive.

## Depends on

- [The k-server problem](../paging-and-k-server/the-k-server-problem.md)
- [No deterministic k-server algorithm beats ratio k](../k-server-on-the-line/deterministic-k-server-lower-bound.md)

## Sources

- Mark S. Manasse, Lyle A. McGeoch, Daniel D. Sleator, "Competitive Algorithms for Server Problems", Journal of Algorithms 11(2) (1990).
- Elias Koutsoupias, "The k-Server Problem", Computer Science Review 3(2) (2009).
