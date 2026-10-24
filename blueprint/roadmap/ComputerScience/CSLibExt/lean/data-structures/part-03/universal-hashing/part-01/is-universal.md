---
article_id: af_f93cb36830419e901292c050
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.UniversalHashing.IsUniversal
---

# Is Universal

A finite hash family is universal if it is nonempty (so that choosing a member
uniformly at random, the reading behind the bound, makes sense) and every two
distinct keys collide under at most a `1 / m` fraction of its members, stated
without division as `collisionCount H x y * m ≤ H.card`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Collision Count](collision-count.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing](../../../../../../../../sources/v2/CSLibExt.md)
