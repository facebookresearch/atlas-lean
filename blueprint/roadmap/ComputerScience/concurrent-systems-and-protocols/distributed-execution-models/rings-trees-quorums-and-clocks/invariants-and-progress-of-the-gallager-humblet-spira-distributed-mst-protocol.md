# Invariants and progress of the Gallager–Humblet–Spira distributed MST protocol

On a connected finite graph with distinct edge weights, the fragment-level model of the Gallager–Humblet–Spira protocol maintains, in every reachable state, that the branch edges are contained in the unique minimum spanning tree, form an acyclic graph whose fragments induce trees, that rejected edges are internal chords of their fragments and not minimum outgoing edges, and that a fragment at level $\ell$ contains at least $2^\ell$ nodes, so levels never exceed $\log_2 n$. From every non-halted state some fragment can absorb or merge along its minimum outgoing edge, and the protocol halts with the minimum spanning tree.

## Proof sketch

By the cut property the minimum outgoing edge of a fragment belongs to the MST. Merging two fragments of equal level raises the level by one and at least doubles the size; absorption of a lower-level fragment preserves the level bound.

## Depends on

- [Asynchronous message-passing systems](../asynchronous-message-passing-systems.md)
- [Prim's algorithm returns a minimum spanning tree](../../../graph-algorithms/spanning-trees-flows-matchings/prim-s-algorithm/prim-minimum-spanning-tree.md)

## Sources

- Robert G. Gallager, Pierre A. Humblet and Philip M. Spira, "A Distributed Algorithm for Minimum-Weight Spanning Trees", ACM Transactions on Programming Languages and Systems, 1983.
