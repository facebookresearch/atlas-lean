---
article_id: af_3fd3b6d1d9aae73018f0d2ba
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.BoundedMultiplicativeFunctionsWanted.BoundedMultiplicativeFunctions.theorem_1_3
---

# Theorem 1 3

Statement of Theorem 1.3 (Non-pretentious multiplicative functions do not correlate
with polynomial phases on short intervals on average):

Let `k : ℕ`, `θ : ℝ` such that `0 < θ < 1/2` and `η : ℝ` such that `η > 0`. Then there exist
constants `Q : ℕ` such that `Q > 0`, `C : ℝ` such that `C > 0`, and `B : ℝ`, such that for any
multiplicative 1-bounded arithmetic function `f : ℕ → ℂ`, any `X : ℝ` such that `X ≥ 1` and any
`H : ℝ` such that `Xᶿ ≤ H ≤ X¹⁻ᶿ`, if

`∫ x ∈ [X, 2X], ‖f‖_{uᵏ⁺¹[x, x + H]}dx ≥ ηX`

then

`M(f;CXᵏ⁺¹/Hᵏ⁺¹,Q) ≤ B`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.BoundedMultiplicativeFunctionsWanted](../../../../../sources/v2/WantedExt.md)
- K. Matomäki, M. Radziwiłł, T. Tao, J. Teräväinen, and T. Ziegler, `Higher uniformity of bounded multiplicative functions in short intervals on average`, Annals of Math, 197 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-2-BoundedMultiplicativeFunctions.lean Via leanprover/lean-eval@38361be, problem `annals_bounded_multiplicative_functions`.
