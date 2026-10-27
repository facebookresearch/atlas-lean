---
article_id: af_d70bd2991e3ac366824900e8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.dilcher_finite_multiple_harmonic_identity
---

# Dilcher finite multiple harmonic identity

Dilcher's finite multiple harmonic identity (Boyadzhiev (2009), equation (26)).

The right side sums over weakly increasing index tuples `1 ≤ j₁ ≤ ⋯ ≤ j_m ≤ n`;
these are represented as monotone functions `js : Fin m → Fin n`, where the shift
`(js i).val + 1` encodes the source indices `1` through `n`.
It follows from `dilcher_finite_multiple_harmonic_identity_general`; the hypothesis `hm` is
unused and keeps the source's shape.
Proves `Wanted` entry `dilcher_finite_multiple_harmonic_identity`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Dilcher finite multiple harmonic identity general](dilcher-finite-multiple-harmonic-identit.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DilcherFiniteMultipleHarmonic](../../../../../sources/v2/MathlibExt.md)
- Khristo N. Boyadzhiev, "Harmonic Number Identities Via Euler's Transform", Journal of Integer Sequences 12 (2009), Article 09.6.1, `https://cs.uwaterloo.ca/journals/JIS/VOL12/Boyadzhiev/boyadzhiev3.tex`, controlling statement equation (26), lines 323–331. Boyadzhiev attributes the identity to Karl Dilcher, "Some q-series identities related to divisor functions", Discrete Mathematics 145 (1995), 83–93, DOI 10.1016/0012-365X(95)00092-B (the JIS bibliography prints "divisor factors").
