---
article_id: af_ae5364053aecb587633e63e6
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BallTree.searchAux
---

# Search Aux

Accumulator similarity search: the points of the tree within squared
distance `radius` of `query`, collected in front of `acc` in linear time.
A node with center `c` and bound `bound` is pruned when
`2 * (bound + radius) < distSq c query`, since by `distSq_le_two_mul` no
point of the subtree can then lie within the query ball.

## Depends on

- [Ball Tree](ball-tree.md)

## Proof depends on

- [Dist Sq](dist-sq.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BallTree](../../../../../../../../sources/v2/CSLibExt.md)
