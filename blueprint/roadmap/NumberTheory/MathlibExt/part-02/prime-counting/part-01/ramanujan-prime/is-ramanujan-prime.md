---
article_id: af_1689d7f7e5c720313ea22cd7
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsRamanujanPrime
---

# Is Ramanujan Prime

A prime `R` satisfies the Ramanujan counting condition for `n`, i.e.
`π(R) - π(R / 2) = n`, where `π` is the prime-counting function.

For natural `R`, `π(R / 2)` (primes `p ≤ R / 2` over the reals) agrees with
`Nat.primeCounting (R / 2)` under `Nat` division.
Concept `jis_sem_2ce4a4483a6ae69670d63026`;
statement `jis_b3eb662622ec0b548e5acec4`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.RamanujanPrime](../../../../../../../sources/v2/MathlibExt.md)
