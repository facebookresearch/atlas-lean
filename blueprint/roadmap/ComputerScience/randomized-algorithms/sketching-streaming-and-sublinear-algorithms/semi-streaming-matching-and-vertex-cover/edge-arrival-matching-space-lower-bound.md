# Space lower bound for beating 1/(1 + ln 2) in single-pass edge-arrival matching

For every constant $\delta > 0$, every randomized single-pass streaming algorithm on insertion-only edge streams of bipartite graphs with $n$ vertices that outputs, with probability at least $1/2$, a matching of size at least

$$
\Big(\frac{1}{1 + \ln 2} + \delta\Big)\,\mu(G), \qquad \frac{1}{1 + \ln 2} \approx 0.5906,
$$

must use $n^{1 + \Omega(1/\log\log n)}$ bits of memory, which exceeds $n \log^{O(1)} n$. Since a $(1 - 1/e)$-approximation ($1 - 1/e \approx 0.632$) is achievable, and optimal, under vertex arrivals in semi-streaming space, this separates the edge-arrival and vertex-arrival semi-streaming models.

## Proof sketch

Online preemptive lower bounds string together several copies of a Karp–Vazirani–Vazirani hard instance using edge arrivals, each copy forcing the algorithm to commit before learning which vertices survive. The proof implements each copy inside a Ruzsa–Szemerédi graph whose induced matchings hide the relevant edges, so that a small-memory algorithm behaves essentially like a preemptive online algorithm on the hidden matching. The factor $1/(1 + \ln 2)$ is that of the online preemptive lower bound of Epstein, Levin, Segev and Weimann that the construction follows, and the density of the Ruzsa–Szemerédi-type graphs used yields the space bound $n^{1 + \Omega(1/\log\log n)}$.

## Depends on

- [Approximate maximum matching and vertex cover in a graph stream](approximate-matching-in-graph-streams.md)
- [Semi-streaming graph model with insertion-only, dynamic and random-order edge streams](semi-streaming-graph-model.md)
- [No single-pass semi-streaming algorithm beats 1 - 1/e for bipartite matching under vertex arrivals](one-minus-inverse-e-barrier-for-streaming-matching.md)

## Proof depends on

- [Ruzsa-Szemerédi graphs: edge sets partitioned into large induced matchings](ruzsa-szemeredi-graphs.md)

## Sources

- Michael Kapralov, "Space Lower Bounds for Approximating Maximum Matching in the Edge Arrival Model", SODA (2021), arXiv:2103.11669.
