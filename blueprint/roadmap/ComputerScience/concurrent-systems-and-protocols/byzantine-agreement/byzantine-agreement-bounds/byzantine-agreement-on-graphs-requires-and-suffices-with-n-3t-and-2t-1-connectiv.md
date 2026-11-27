# Byzantine agreement on graphs requires and suffices with n > 3t and (2t + 1)-connectivity

For a fixed number of rounds large enough, Boolean Byzantine agreement against $t$ faults is solvable on a communication graph $G$ with $n$ vertices if and only if $n \le 1$, or $n > 3t$ and $G$ is $(2t + 1)$-vertex-connected. Sufficiency is achieved by simulating the oral messages algorithm over $2t + 1$ internally disjoint paths between every pair of processes and taking majority values.

## Proof sketch

By Menger's theorem $(2t + 1)$-connectivity provides $2t + 1$ internally disjoint paths, at most $t$ of which contain faulty relays, so majority over paths delivers each correct message faithfully; the complete-graph algorithm then runs in epochs.

## Depends on

- [Byzantine agreement on a communication graph](byzantine-agreement-on-a-communication-graph.md)
- [Menger's theorem, vertex form](../../../../GraphTheory/paths-cycles-connectivity/menger-s-theorem/menger-vertex.md)

## Proof depends on

- [No Byzantine agreement across a vertex separator of size at most 2t](no-byzantine-agreement-across-a-vertex-separator-of-size-at-most-2t.md)
- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../not-solves-of-card-le-three-mul.md)
- [The oral messages algorithm solves the Byzantine generals problem](../../byzantine-generals-problem/byzantine-generals.md)

## Sources

- Danny Dolev, "The Byzantine Generals Strike Again", Journal of Algorithms, 1982.
- Michael J. Fischer, Nancy A. Lynch and Michael Merritt, "Easy Impossibility Proofs for Distributed Consensus Problems", Proceedings of the Fourth Annual ACM Symposium on Principles of Distributed Computing, 1985.
