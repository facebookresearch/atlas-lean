---
article_id: af_e2723240dbf7a13f6ddae5bd
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.UniversalCycleSubsetsWanted.IsUniversalCycle
---

# Is Universal Cycle

Universal cycle for the `k`-subsets of an `n`-set, in the sense of
Chung/Diaconis/Graham as cited in Cooper, Combinatorial Problems I Like,
Words and Codes bullet 78 [AMR-030-0078]: a cyclic sequence `c` of length
`Nat.choose n k` over `Fin n` such that every block of `k` consecutive cyclic
entries has cardinality `k` and every `k`-subset of `Fin n` occurs as such a
block for exactly one starting position.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.UniversalCycleSubsetsWanted](../../../../../sources/v2/WantedExt.md)
