---
article_id: af_1f56244275cf8f3ab11d1e21
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.gauss_hypergeometric_summation_klamkin
---

# Gauss hypergeometric summation klamkin

Klamkin's summation: `₂F₁(n, b + 1; b - a; 1)` equals
`Γ(-a - n - 1) Γ(b - a) / (Γ(b - a - n) Γ(-a - 1))`, under the source
conditions `-a ∉ ℕ`, `-b ∉ ℕ`, `1 ≤ n`, the convergence condition
`-a - 1 > n` (i.e. `a + 1 + n < 0`), and the admissibility condition
`a - b + 1 ∉ ℕ`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.GaussHypergeometricSummationKlamkin](../../../../../../../sources/v2/MathlibExt.md)
- U. Abel, "A Short Proof of the Binomial Identities of Frisch and Klamkin," _Journal of Integer Sequences_ 23 (2020), Article 20.7.1.
