---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.isSignedPowTwoSum_iff
---

# Is Signed Pow Two Sum iff

Interval and congruence characterization of signed power-of-two sums.

Verified by brute-force enumeration for `m ∈ {1, 2, 3, 5}`, `s ≤ 2`,
`t - s ≤ 3` before formalizing.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.SignedBinarySumWanted](../../../../../sources/v2/WantedExt.md)
- Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 7 (`jis-2024-24.7.5-lem-7`): for `0 ≤ s ≤ t` and `m ≥ 1`, the integers of the form `∑_{j=s}^{t} λⱼ * 2^j` with `λⱼ ∈ {-1, m}` are precisely the integers `n` in the interval `[-2^s * (2^{t-s+1} - 1), 2^s * m * (2^{t-s+1} - 1)]` satisfying `n ≡ -2^s * (2^{t-s+1} - 1) [ZMOD 2^s * (m + 1)]`.
