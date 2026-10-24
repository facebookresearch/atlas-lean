---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.ZagierHoffmanPositiveCharWanted.ZagierHoffmanPositiveChar.theorem_D
---

# Theorem D

Statement of Theorem D:

Let `w ∈ ℕ+` with `w ≤ 2q − 2`. Then `𝒯 w` is a `K`-basis for `𝒵 w`. In particular,
`dim_K (𝒵 w) = d(w)`. Note that `K` in the paper is `RatFunc F`.

Note: Theorem A establishes that `𝒯 w` spans `𝒵 w`. So to prove `𝒯 w` is a `K`-basis for `𝒵 w`, we
only need to show that `𝒯 w` are linearly independent in `𝒵 w`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ZagierHoffmanPositiveCharWanted](../../../../../sources/v2/WantedExt.md)
- T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean Via leanprover/lean-eval@38361be, problem `annals_zagier_hoffman_positive_char`.
