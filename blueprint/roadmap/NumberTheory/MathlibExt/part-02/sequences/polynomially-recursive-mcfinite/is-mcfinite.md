---
article_id: af_2daf4bcf6dcfbe766c9a2464
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsMCFinite
---

# Is MCFinite

An integer sequence `s` is MC-finite if for every modulus `m > 0` it eventually satisfies,
modulo `m`, a linear recurrence with constant integer coefficients: there are `p, q > 0` and
`c₀, …, c_{p-1}` with `s (n + p) ≡ ∑ i < p, cᵢ s (n + i) [ZMOD m]` for all `n ≥ q`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Sequences.PolynomiallyRecursiveMCFinite](../../../../../../sources/v2/MathlibExt.md)
- Filmus, Fischer, Makowsky, and Rakita, "MC-Finiteness of Restricted Set Partition Functions," Journal of Integer Sequences 26 (2023), Article 23.7.4, lines 281–286.
