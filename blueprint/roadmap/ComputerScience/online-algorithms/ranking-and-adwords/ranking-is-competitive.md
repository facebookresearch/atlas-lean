# RANKING is (1 - 1/e)-competitive

For every finite offline vertex set $L$, every arrival sequence and every matching $M$ of the graph of the arrivals,

$$
\mathbb{E}\big[\,|\text{RANKING}|\,\big] \ge \Big(1 - \frac{1}{e}\Big)|M| .
$$

## Proof sketch

Randomized primal-dual (Devanur-Jain-Kleinberg): replace the rank order by independent uniform $y_u \in [0, 1]$ and, when $v$ is matched to $u$, split the unit gain as $g(y_u)$ to $u$ and $1 - g(y_u)$ to $v$ with $g(y) = e^{y-1}$. Show that the expected dual is feasible up to the factor $1 - 1/e$ for every edge by a monotonicity and dominance argument over $y_u$, and conclude by weak duality.

## Depends on

- [The RANKING algorithm](ranking-algorithm.md)
- [Greedy online matching is $1/2$-competitive](../online-bipartite-matching/card-le-two-mul-greedy-all.md)

## Sources

- R. M. Karp, U. V. Vazirani and V. V. Vazirani, "An Optimal Algorithm for On-line Bipartite Matching", Proceedings of the 22nd ACM Symposium on Theory of Computing (STOC), 1990.
- N. R. Devanur, K. Jain and R. D. Kleinberg, "Randomized Primal-Dual Analysis of RANKING for Online Bipartite Matching", Proceedings of the 24th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2013.
