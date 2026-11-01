---
article_id: af_89e1a32687b84132c46262c4
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.blockSum
---

# Block Sum

The interval sum stored at one-indexed position `j`: the sum of the
`lowbit j` entries of `arr` ending at position `j - 1`, with entries past the end
reading as `0`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lowbit](lowbit.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
