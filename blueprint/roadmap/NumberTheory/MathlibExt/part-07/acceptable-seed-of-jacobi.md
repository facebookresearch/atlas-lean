---
article_id: af_e93dd6441540549b45bb1dfa
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.acceptableSeed_of_jacobi
---

# Lucas Lehmer Acceptable Seed

A seed `s₁` is acceptable for the Lucas-Lehmer test on `Mₙ` (Assertion A: the
test diagnoses primality of `Mₙ`) when the two Jacobi-symbol conditions hold.
Here `Mₙ = mersenne n` and `sₙ₋₁` is the `(n - 2)`-fold iterate of
`x ↦ x^2 - 2` starting from `s₁`.

Proof: Following Mathlib's Lucas-Lehmer order argument, sufficiency uses a quadratic extension
and the least prime factor; necessity uses the Jacobi conditions and Frobenius conjugation as in
Lehmer (1930) and Roettger-Williams (2025).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.LucasLehmerAcceptableSeed](../../../../sources/v2/MathlibExt.md)
- E. L. Roettger and H. C. Williams, "Some Remarks Concerning the Lucas-Lehmer Primality Test," Journal of Integer Sequences 28 (2025), Article 25.2.5, Theorem (label acceptableseed), lines 814–819; Assertion A (label assertionA) at lines 187–190, https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.tex
