---
article_id: af_d1047fab93e5848c8802a129
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.KdTree.reportAux
---

# Report Aux

Accumulator form of the orthogonal range report: `reportAux t lo hi acc`
prepends the reported points (in left-to-right order) onto `acc`. The
accumulator avoids repeatedly appending left results, so constructing the
output list costs only work linear in the number of reported points; the
traversal itself still visits every node that pruning does not cut, which
can be the whole tree even for an empty report, and no complexity bound is
proved here. At a split node with axis `a` and value `s`, the left child is
pruned when `s < lo a` and the right child is pruned when `hi a < s`.

## Depends on

- [Kd Tree](kd-tree.md)

## Proof depends on

- [In Box](in-box.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.KdTree](../../../../../../../../sources/v2/CSLibExt.md)
