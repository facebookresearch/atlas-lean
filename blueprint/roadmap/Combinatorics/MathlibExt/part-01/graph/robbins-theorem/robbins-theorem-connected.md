---
article_id: af_f299ff31bf41d5a48f1ae654
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.robbins_theorem_connected
---

# Robbins theorem connected

Robbins' theorem, standard connected formulation
(https://en.wikipedia.org/wiki/Robbins%27_theorem): a finite nonempty undirected simple
graph is 2-edge-connected (connected and bridgeless, with bridgelessness expressed as
reachability after deleting any single edge) if and only if it admits a strongly connected
orientation.

Primary source: H. E. Robbins, "A Theorem on Graphs, with an Application to a Problem
of Traffic Control," American Mathematical Monthly 46 (1939), 281–283.

`robbins_theorem` is the `G.Preconnected` variant of this statement, which additionally
holds vacuously for the empty graph.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Graph.RobbinsTheorem](../../../../../../sources/v2/MathlibExt.md)
