# Sharp load thresholds for d-ary cuckoo hashing

For each $d \ge 3$ let $\xi_d > 0$ be the unique solution of $d = \frac{\xi(e^{\xi} - 1)}{e^{\xi} - 1 - \xi}$ and set $c_d^* = \frac{\xi_d}{d\,(1 - e^{-\xi_d})^{d-1}}$. For every fixed $c < c_d^*$, a valid assignment of $n = cm$ random keys exists with probability $1 - o(1)$ as $m \to \infty$, and for every fixed $c > c_d^*$ no valid assignment exists with probability $1 - o(1)$. Numerically $c_3^* \approx 0.918$ and $c_4^* \approx 0.977$; for $d = 2$ the threshold is $1/2$.

## Proof sketch

Validity is the orientability of a random $d$-uniform hypergraph whose vertices are slots and whose hyperedges are keys. Peeling a vertex of degree at most one together with its hyperedge preserves orientability in both directions, so an assignment exists if and only if the $2$-core satisfies Hall's condition: every set $F$ of hyperedges of the core spans at least $|F|$ vertices. This is Hall's marriage theorem for the bipartite incidence graph between hyperedges (keys) and vertices (slots), in which a matching saturating the keys is exactly an assignment. The core's numbers of vertices and hyperedges are computed from the fixed point $\xi_d$ of a Poisson branching recursion. Above $c_d^*$ the whole core has more hyperedges than vertices, so Hall's condition fails. Below $c_d^*$ the whole core has fewer hyperedges than vertices, but this alone does not control its subsets: a hypergraph can have as many vertices as hyperedges and still contain a set of hyperedges spanning fewer vertices. Fountoulakis and Panagiotou add a probabilistic step showing that, with probability $1 - o(1)$, no set of hyperedges of the core spans fewer vertices than its size, which yields the stated threshold.

## Depends on

- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)

## Sources

- Martin Dietzfelbinger, Andreas Goerdt, Michael Mitzenmacher, Andrea Montanari, Rasmus Pagh, Michael Rink, "Tight Thresholds for Cuckoo Hashing via XORSAT", ICALP (2010), arXiv:0912.0287.
- Nikolaos Fountoulakis, Konstantinos Panagiotou, "Sharp Load Thresholds for Cuckoo Hashing", Random Structures and Algorithms 41(3) (2012).
- Alan Frieze, Páll Melsted, "Maximum Matchings in Random Bipartite Graphs and the Space Utilization of Cuckoo Hash Tables", Random Structures and Algorithms 41(3) (2012).
