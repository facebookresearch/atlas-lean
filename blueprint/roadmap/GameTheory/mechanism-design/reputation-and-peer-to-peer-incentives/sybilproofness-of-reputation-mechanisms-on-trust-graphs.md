# Sybilproofness of reputation mechanisms on trust graphs

On transitive trust graphs (nonnegative directed edge weights), a sybil strategy lets a node replace itself by any set of nodes with arbitrary internal trust edges, keeping the incoming edges. No nontrivial symmetric global reputation function (invariant under graph isomorphism) is rank-sybilproof, or even $K$-rank-sybilproof for $K \ge 1$, and none that is also monotonic (adding an incoming edge to a node never lowers its rank relative to any other node) is rank-strategyproof (no node can improve its rank by changing its own outgoing trust edges). The seeded max-flow reputation (maximum flow from a fixed seed) is value-sybilproof but not rank-sybilproof, while seeded shortest-path (Pathrank) reputation is value- and rank-sybilproof.

## Proof sketch

For symmetric functions, a node can create a copy of the whole graph structure around a better-ranked node and gain its rank by symmetry. For seeded max flow, every cut separating the seed from the node is unaffected by edges the node creates, so its value cannot increase; Pathrank distances can only grow under sybil creation.

## Depends on

- [Max-flow min-cut theorem](../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)

## Sources

- Alice Cheng and Eric Friedman, "Sybilproof Reputation Mechanisms", Proceedings of the 2005 ACM SIGCOMM Workshop on Economics of Peer-to-Peer Systems (P2PECON '05), 2005.
- Eric Friedman, Paul Resnick and Rahul Sami, "Manipulation-Resistant Reputation Systems", Algorithmic Game Theory, Cambridge University Press, 2007.
