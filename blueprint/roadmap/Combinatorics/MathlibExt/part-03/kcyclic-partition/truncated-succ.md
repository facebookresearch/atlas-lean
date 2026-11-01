---
article_id: af_d641ebe1c8b604ee9e95e3f3
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TruncatedSucc
---

# Truncated Succ

Truncated-cycle successor for a permutation `σ` at label `i`.

It characterizes the exact evaluation `σ^(i)(i) = j` as the first positive
forward iterate `(σ ^ m) i` whose label is `≤ i`: there exists `m > 0` with
`(σ ^ m) i = j`, `j ≤ i`, and every earlier positive iterate has label `> i`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.KCyclicPartition](../../../../../sources/v2/MathlibExt.md)
