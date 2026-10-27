---
article_id: af_213b247de06805c815362f33
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.BTree.maxKey
---

# Max Key

The greatest key of a tree, found by descending the rightmost spine:
at each internal node, recurse into the last child only. Each step splits
a child list of length at most `2 * t`, so on a valid tree this costs
`O(t * height)`; it never materializes the flattening. The characterization
as the last key of the flattening is `exists_maxKey_flatten` below.

## Depends on

- [BTree](../../../btree-2/part-01/btree.md)

## Proof depends on

- [Split Last](split-last.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.BTree.DeleteBalanced](../../../../../../../../../sources/v2/CSLibExt.md)
