# Correctness of Dinitz's algorithm

**Dinitz's algorithm** repeatedly computes the level network of the residual network, finds a blocking flow in it (greedily, by augmenting along paths of unsaturated level arcs by their bottleneck until none remains), and augments, until $t$ is not residually reachable. On a network with integral capacities and $s \ne t$ it returns a maximum flow together with a minimum $s$-$t$ cut of equal value, after at most $|V| - 1$ phases, each consisting of at most $|A^+|$ bottleneck augmentations, where $A^+$ is the set of arcs of positive capacity.

## Proof sketch

Each bottleneck augmentation saturates at least one level arc, which stays saturated within the phase. Termination follows from the phase lemma, and at termination the reachable set gives a cut whose capacity equals the flow value.

## Depends on

- [Level networks and blocking flows](level-networks-and-blocking-flows.md)
- [Max-flow min-cut theorem](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)

## Proof depends on

- [Dinitz phase lemma](dinitz-phase-lemma.md)
- [Weak duality for flows and cuts](../../../../GraphTheory/matchings-and-flows/max-flow-min-cut-theorem/flow-value-le-cut-capacity.md)

## Sources

- E. A. Dinic, "Algorithm for Solution of a Problem of Maximum Flow in Networks with Power Estimation", Soviet Mathematics Doklady 11, 1970.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
