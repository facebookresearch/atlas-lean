# Finding a negative sandwich or a 1-hop independent set of size Omega(k^{1/3}) in O(m log^2 n) time

Let $G=(V,E^{+}\cup E^{-},w)$ with $w\ge 0$ on $E^{+}$, $n$ vertices, $m$ edges and $k=|E^{-}|$ negative edges. There is a Las Vegas randomized algorithm running in $O(m\log^2 n)$ time with high probability that always does one of the following: (1) correctly reports a negative cycle; (2) returns a negative sandwich $(x,U,y)$ with $|U|=\Omega(k^{1/3})$; (3) returns a $1$-hop independent set $I$ with $|I|=\Omega(k^{1/3})$. Given a $1$-hop independent set $I$, a valid price function neutralizing all negative edges of $I$, or a negative cycle, is obtained from the Johnson potentials $d^1(V,\cdot)$ of the subgraph keeping only the negative edges of $I$, in $O(m+n\log n)$ time.

## Proof sketch

A one-sided primitive, run with $\rho=\lceil k^{1/3}\rceil$, either finds a $1$-hop independent set of size $\Omega(\rho)$ or a vertex $y$ with a set $U_1$ of $\Omega(k/\rho)=\Omega(k^{2/3})$ negative vertices satisfying $d^1(u,y)<0$; it classifies vertices $v$ as heavy or light by estimating, from $O(\log n)$ random samples of rate $\rho/k$, how many candidates reach $v$ by a negative $1$-hop path, returns a heavy $y$ with its set $U_1$ if one exists, and otherwise samples a random set $I'$ of $\Theta(\rho)$ candidates and keeps $I=I'\setminus R^1(I')$, which is independent and has size $\Omega(\rho)$ with constant probability. Running the primitive again on the transpose graph restricted to $U_1$ either yields an independent set or a vertex $x$ with $\Omega(|U_1|/\rho)=\Omega(k^{1/3})$ vertices $u\in U_1$ with $d^1(x,u)<0$, which together with $y$ is a negative sandwich. For an independent set, every shortest walk into the subgraph uses at most one hop, so $d(V,\cdot)=d^1(V,\cdot)$ there.

## Depends on

- [beta-betweenness of vertex pairs and negative sandwiches of negative vertices](beta-betweenness-and-negative-sandwiches.md)
- [r-remote sets and 1-hop independent sets of negative vertices](remote-and-independent-negative-sets.md)
- [Negative vertices, h-hop distances and the negative h-hop reach](negative-vertices-and-hop-distances.md)
- [Price functions, reduced edge weights, and valid reweightings of a directed graph](../near-linear-negative-weight-sssp/price-functions-and-reduced-weights.md)

## Proof depends on

- [Computing h-hop distances by alternating Dijkstra and Bellman-Ford rounds in O(h(m + n log n)) time](hop-limited-distances-hybrid.md)

## Sources

- Jeremy T. Fineman, "Single-Source Shortest Paths with Negative Real Weights in Õ(mn^(8/9)) Time", STOC (2024), arXiv:2311.02520.
