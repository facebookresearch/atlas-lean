---
article_id: af_43bc47742099546ef6d45fea
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.EulerTourTree.Tree.children_ind
---

# Children ind

Induction on a tree from the statement for every child subtree. The built-in
`induction` tactic does not support the nested recursion through `List`, so this
principle is derived from `Tree.rec` and used with `induction … using`.

## Depends on

- [Tree](tree.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.EulerTourTree](../../../../../../../../sources/v2/CSLibExt.md)
