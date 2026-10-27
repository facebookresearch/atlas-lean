---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.PseudorandomGrassmannWanted.PseudorandomGrassmann.theorem_1_12
---

# Theorem 1 12

Statement of Theorem 1.12:

For every constant `0 < α < 1`, there exist a constant `ε > 0` and an
integer `r ≥ 0` such that for all sufficiently large integers `ℓ` and (after fixing it)
for all sufficiently large integers `k`, the following holds. Let `S ⊆ Grₖₗ` be such that
`Φ(S) ≤ α`. Then there exist subspaces `A ⊆ B ⊆ 𝔽₂ᵏ` such that `dim(A) = a`, `codim(B) = b`,
`a + b ≤ r` and `|S ∩ Grₖₗ[A,B]| / |Grₖₗ[A,B]| ≥ ε`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.PseudorandomGrassmannWanted](../../../../../sources/v2/WantedExt.md)
- S. Khot, D. Minzer, and M. Safra, `Pseudorandom sets in Grassmann graph have near-perfect expansion`, Annals of Math, 198 (1) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-198-1-PseudorandomGrassmann.lean Via leanprover/lean-eval@38361be, problem `annals_pseudorandom_grassmann`.
