---
article_id: af_6bcf95a2c76be4e5577bb74e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.primePrimes_oneBased_ratio_tendsto_one
---

# Prime Primes one Based ratio tendsto one

Part (c) of the Broughan–Barnett corollary in the source's one-based indexing.
With zero-based `Nat.nth`, the source's `q_n = p_{p_n}` (with `p_1 = 2`) is
`Nat.nth Nat.Prime (Nat.nth Nat.Prime n - 1)`, and
`primePrimes_ratio_tendsto_one` is the same limit for the shifted
sequence `p_{p_n + 1}`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Prime Number Theorem](../../../../part-09/prime-number-theorem.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.PrimePrimeRatio](../../../../../../../sources/v2/MathlibExt.md)
