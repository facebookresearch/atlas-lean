# Betweenness reduction: one reweighting makes every pair have beta-betweenness at most n/tau

Let $G=(V,E^{+}\cup E^{-},w)$ with $w(e)\ge 0$ on $E^{+}$, $n$ vertices and $m$ edges, and let $\beta,\tau\ge 1$ be integers. There is a Monte Carlo randomized algorithm running in $\tilde O(\beta\tau m+\tau^2 n)$ time that always does one of the following, and with high probability one of the first two: (1) correctly reports a negative cycle; (2) returns a valid price function $\phi$ with $\mathrm{BW}^\beta_\phi(u,v)\le n/\tau$ for all $u,v\in V$; (3) returns a valid price function for which this betweenness bound fails.

## Proof sketch

Sample $\Theta(\tau\log n)$ vertices and compute a valid reweighting under which all $\beta$-hop distances to and from sampled vertices are nonnegative, using hop-limited distance computations of total cost $\tilde O(\beta\tau m)$ plus $\tilde O(\tau^2 n)$ bookkeeping, or detect a negative cycle. Fix $u,v$; since $\mathrm{thru}^\beta$ shifts by $\phi(u)-\phi(v)$ independently of the middle vertex, the order of through-distances is preserved. With high probability some sample $y$ lies among the $n/\tau$ vertices of smallest through-distance, and after reweighting $\mathrm{thru}^\beta_\phi(u,y,v)\ge 0$, so every vertex with larger through-distance is not $\beta$-between $u$ and $v$; a union bound over pairs completes the argument.

## Depends on

- [beta-betweenness of vertex pairs and negative sandwiches of negative vertices](beta-betweenness-and-negative-sandwiches.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](../near-linear-negative-weight-sssp/price-functions-and-reduced-weights.md)

## Proof depends on

- [Computing h-hop distances by alternating Dijkstra and Bellman-Ford rounds in O((h + 1)(m + n log n)) time](hop-limited-distances-hybrid.md)
- [Reweighting by a price function shifts every distance by the endpoint prices and preserves cycle weights](../near-linear-negative-weight-sssp/price-function-distance-shift.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
