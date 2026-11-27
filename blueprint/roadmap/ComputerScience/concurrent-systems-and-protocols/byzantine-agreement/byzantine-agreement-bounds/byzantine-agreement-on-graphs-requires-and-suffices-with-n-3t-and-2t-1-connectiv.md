# Byzantine agreement on graphs requires and suffices with n > 3t and (2t + 1)-connectivity

Let $t \ge 1$ and let $G$ be a communication graph with $n \ge 3$ vertices. If $n \le 3t$ or $G$ is not $(2t + 1)$-vertex-connected, no protocol solves Boolean Byzantine agreement against $t$ faults on $G$ (Fischer, Lynch and Merritt, Theorem 1). Conversely, if $n > 3t$ and $G$ is $(2t + 1)$-vertex-connected, then for every transmitter $v$ Dolev's synchronous algorithm $\mathrm{BG}(G, v, V \setminus \{v\}, t, t)$ solves the Byzantine generals problem against $t$ faults: all correct receivers agree on the same value, and if the transmitter is correct they agree on its value (Dolev, Corollary 10, via Theorems 1 and 9).

## Proof sketch

Necessity: a graph with fewer than $3t + 1$ vertices or connectivity less than $2t + 1$ is covered by a larger system whose behaviours splice into correct behaviours of $G$ that force contradictory choices. Sufficiency: by Menger's theorem $(2t + 1)$-connectivity provides $2t + 1$ internally disjoint paths between any two processes, at most $t$ of which contain faulty relays, so a correct transmitter's value reaches every correct receiver (Dolev, Theorem 1; in synchronous rounds a majority over the paths suffices); the oral-messages recursion then runs over these simulated links (Dolev, Theorem 9). For all-input agreement with $n > 3t$, every process can broadcast its input this way and all decide the majority of the received inputs, which is valid because $n - t > n/2$; this derived step is not stated in the cited sources.

## Depends on

- [Byzantine agreement on a communication graph](byzantine-agreement-on-a-communication-graph.md)
- [Menger's theorem, vertex form](../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/menger-vertex.md)

## Proof depends on

- [No Byzantine agreement across a vertex separator of size at most 2t](no-byzantine-agreement-across-a-vertex-separator-of-size-at-most-2t.md)
- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../not-solves-of-card-le-three-mul.md)
- [The oral messages algorithm solves the Byzantine generals problem](../../byzantine-generals-problem/byzantine-generals.md)

## Sources

- Danny Dolev, "The Byzantine Generals Strike Again", Journal of Algorithms 3(1), 1982 (author version: Stanford report STAN-CS-81-846, 1981), Theorem 1, Theorem 9 and Corollary 10.
- Michael J. Fischer, Nancy A. Lynch and Michael Merritt, "Easy Impossibility Proofs for Distributed Consensus Problems", Distributed Computing 1(1), 1986, §3, Theorem 1.
