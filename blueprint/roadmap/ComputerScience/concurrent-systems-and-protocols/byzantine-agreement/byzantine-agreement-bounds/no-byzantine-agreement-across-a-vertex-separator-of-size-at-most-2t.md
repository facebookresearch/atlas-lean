# No Byzantine agreement across a vertex separator of size at most 2t

Let $G$ be a communication graph with two vertices $u, v$ separated by a set $C$ of at most $2t$ vertices (every $u$–$v$ path meets $C$, and $u, v \notin C$). Then no deterministic synchronous protocol solves Boolean Byzantine agreement on $G$ against $t$ faults, for any fixed number of rounds. Consequently Byzantine agreement on a non-complete graph $G$ requires $G$ to be $(2t + 1)$-vertex-connected.

## Proof sketch

Split $C$ into two halves of size at most $t$. Build a covering network from two copies of $G$ with all inputs $0$ and $1$ respectively, rewired across the separator; each local view in the cover coincides with a run of $G$ in which one half of $C$ is faulty, so validity forces opposite decisions on two sides that must agree in some run.

## Depends on

- [Byzantine agreement on a communication graph](byzantine-agreement-on-a-communication-graph.md)
- [Characterization of $k$-vertex-connectivity by vertex deletion](../../../../GraphTheory/paths-cycles-connectivity/vertex-connectivity/is-vertex-connected-iff.md)

## Proof depends on

- [No synchronous protocol reaches Byzantine agreement when $3 \le n \le 3m$](../not-solves-of-card-le-three-mul.md)

## Sources

- Michael J. Fischer, Nancy A. Lynch and Michael Merritt, "Easy Impossibility Proofs for Distributed Consensus Problems", Proceedings of the Fourth Annual ACM Symposium on Principles of Distributed Computing, 1985.
