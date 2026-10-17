---
article_id: af_75e81eb53a1f257bbe10f52f
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.FenwickTree.prefixSum
---

# Prefix Sum

The sum of the first `k` underlying entries, computed by walking the stored
entries at `k, k - lowbit k, …` down to `0`. Indices past the end are clamped:
querying at `k` greater than the size sums the whole represented array, just
like `List.take`.

## Depends on

- [Fenwick Tree](fenwick-tree.md)

## Proof depends on

- [Lowbit](lowbit.md)
- [Size](size.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FenwickTree](../../../../../../../../sources/v2/CSLibExt.md)
