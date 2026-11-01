---
article_id: af_3b8840020e14b0aa72c92891
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.CartesianTree.splitAtFirst_not_mem_fst
---

# Split At First not mem fst

Splitting at the *first* occurrence: the split value does not occur in
the left part. Together with the reconstruction equation in
`splitAtFirst_spec`, this characterizes the split point (including the
duplicate tie-breaking behavior used by `build`) without unfolding the
definition: reconstruction alone would hold for a split at any
occurrence.

## Depends on

- [Split At First](split-at-first.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.CartesianTree](../../../../../../../sources/v2/CSLibExt.md)
