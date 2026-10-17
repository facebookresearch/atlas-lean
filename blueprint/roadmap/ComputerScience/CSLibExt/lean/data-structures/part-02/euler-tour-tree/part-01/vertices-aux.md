---
article_id: af_b0026a68f668a7d18c83054c
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.EulerTourTree.Tree.verticesAux
---

# Vertices Aux

Accumulator preorder traversal: `verticesAux t acc = vertices t ++ acc`
(see `verticesAux_eq`), so `vertices` is linear rather than repeatedly
appending child lists.

## Depends on

- [Tree](tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.EulerTourTree](../../../../../../../../sources/v2/CSLibExt.md)
