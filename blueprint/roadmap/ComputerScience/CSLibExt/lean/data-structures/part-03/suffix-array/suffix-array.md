---
article_id: af_4e09a4ffb8f402e62995f60b
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.SuffixArray.suffixArray
---

# Suffix Array

The suffix array of `s`: the indices `0 … s.length - 1` sorted by their suffixes
in lexicographic order. Equal suffixes cannot occur for distinct in-range indices
(their lengths differ), so the sorted order agrees with the usual specification up
to the merge sort's handling of the comparison.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Suffix](suffix.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.SuffixArray](../../../../../../../sources/v2/CSLibExt.md)
