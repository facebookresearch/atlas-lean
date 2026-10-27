---
article_id: af_295b15e8d8fd93f9a9b21fe5
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.laishram_ramanujan_prime_bound
---

# Laishram Ramanujan Prime Bound Wanted

Laishram upper bound for the nth Ramanujan prime (JIS THM laishram):
if `R` is the nth Ramanujan prime, in the sense of the existing predicate
`IsNthRamanujanPrime` (which already contains positivity of `n`),
then `R < p_{3n}` (one-indexed), stated with zero-indexed
`Nat.nth Nat.Prime (3 * n - 1)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.LaishramRamanujanPrimeBoundWanted](../../../../../../sources/v2/WantedExt.md)
- https://cs.uwaterloo.ca/journals/JIS/VOL14/Noe/noe12.tex, source file SHA-256 b63cf16b83caaaf31e14592b36ef720cdb8c29d7acb1d0c51fad733e550756c6, THM laishram lines 152-160, exact span SHA-256 4cf034f71bb4dd02bd70f5464b47630035176520d6e76ae976119bc050561a5b, definition lines 105-117, exact span SHA-256 aa194a945f450eec09898ade174650294052937acdca5139e43f57f9adb760c0, task jis_grounded_1c4ec8bb1841443d9a65cadf__laishram_ramanujan_prime_bound.
