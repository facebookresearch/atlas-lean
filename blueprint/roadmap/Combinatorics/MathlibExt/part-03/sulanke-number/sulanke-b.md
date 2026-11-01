---
article_id: af_5e015bfc83db78e0ae7aed65
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.sulankeB
---

# Sulanke B

Sulanke `B` array from the JIS clause: `B 0 = (1, 0, ...)`,
`B (k+1)` is built from `B k` by eliminating the intermediate `A` row,
so `B (k+1) 0 = B k 0` and
`B (k+1) (i+1) = (B k (i+1) + 2 * B k i) + (B k i + 2 * B k (i - 1))`
with the value below zero read as `0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SulankeNumber](../../../../../sources/v2/MathlibExt.md)
