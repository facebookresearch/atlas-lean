---
article_id: af_f5620f0bd9fe95088c1f37e9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.robbins_theorem
---

# Robbins theorem

Robbins' theorem (https://en.wikipedia.org/wiki/Robbins%27_theorem): a finite
undirected simple graph is 2-edge-connected (preconnected and bridgeless, with
bridgelessness expressed as reachability after deleting any single edge) if and
only if it admits a strongly connected orientation.

The connectivity hypothesis is `G.Preconnected` (`∀ u v, G.Reachable u v`), which holds
vacuously when `V` is empty: both sides of this formulation are true for the empty graph,
so this extends the standard `G.Connected` formulation to the empty graph (see
`robbins_theorem_connected`, which assumes `[Nonempty V]`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Robbins theorem connected](robbins-theorem-connected.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Graph.RobbinsTheorem](../../../../../../sources/v2/MathlibExt.md)
