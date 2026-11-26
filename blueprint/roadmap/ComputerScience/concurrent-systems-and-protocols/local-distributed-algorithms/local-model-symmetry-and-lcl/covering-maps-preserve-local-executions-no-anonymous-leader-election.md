# Covering maps preserve LOCAL executions; no anonymous leader election

In the synchronous LOCAL model on locally finite graphs, either with broadcast of multisets of messages or with port numbering and local inputs, let $\phi : H \to G$ be a covering map (a surjective graph homomorphism that is a bijection on every closed neighbourhood, respecting ports and inputs). Then for every deterministic anonymous protocol and every round, each vertex of $H$ is in the same state as its image in $G$. Consequently no deterministic anonymous protocol elects a unique leader on a graph that is a nontrivial cover of another network, for example on a ring $C_{km}$ with $k \ge 2$, $m \ge 3$ and identical inputs (a $k$-fold cover of $C_m$), or on bipartite double covers.

## Proof sketch

Induction on rounds: corresponding vertices start in the same state and receive the same multiset of messages because the covering map is a bijection on neighbourhoods. A unique leader in $H$ would have all its preimage-mates elected as well.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [No deterministic leader election on an anonymous ring](../../leader-election-on-anonymous-rings/no-leader-election.md)

## Sources

- Dana Angluin, "Local and Global Properties in Networks of Processors", Proceedings of the Twelfth Annual ACM Symposium on Theory of Computing (STOC 1980), 1980.
- Juho Hirvonen and Jukka Suomela, "Distributed Algorithms 2020", Online textbook, Aalto University, 2020.
