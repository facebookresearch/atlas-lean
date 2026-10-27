---
article_id: af_492ba95de70ca71275af8b87
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry12SummableSuccN.ramanujan_part1_ch3_entry12_summable_succ_n_general
---

# Ramanujan part1 ch3 entry12 summable succ n general

`ramanujan_part1_ch3_entry12_summable_succ_n` without the hypothesis that `n + k ≠ 0` whenever
 `0 ≤ k` and `r + k < 0`. This is a statement about Lean's totalized `zpow`: at an index where
 `n + k = 0` and the exponent `r + 1 + k` is negative, the term is `0 ^ (r + 1 + k) = 0`, whereas
 the source's term is undefined there. Summability depends only on the tail, where every exponent
 is nonnegative.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry12SummableSuccN](../../../../../../../sources/v2/MathlibExt.md)
