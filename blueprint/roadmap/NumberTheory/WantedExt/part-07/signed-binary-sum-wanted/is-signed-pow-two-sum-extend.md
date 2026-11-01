---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.isSignedPowTwoSum_extend
---

# Is Signed Pow Two Sum extend

Extension of signed power-of-two sums to longer intervals.

The hypothesis `t ≥ s + β - 1` is written as `s + β ≤ t + 1` to cover the
case `β = 0`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.SignedBinarySumWanted](../../../../../sources/v2/WantedExt.md)
- Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Corollary 8 (`jis-2024-24.7.5-cor-8`): fix `m ≥ 1` and let `β = ν₂(m + 1)`. If `n` is a signed power-of-two sum over `[s, t]` with `t ≥ s + β - 1`, then `n` is also expressible over `[s, t + α]` whenever `2^α ≡ 1 [(m + 1) / 2^β]`.
