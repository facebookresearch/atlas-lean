---
article_id: af_a8bbf9a17d66c7a52348182d
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Geometry.BoseGasesWanted.BoseGases.theorem_1_2
---

# Theorem 1 2

Statement of Theorem 1.2 (The Lee-Huang-Yang Formula):

For any non-zero, non-negative, radial potential `v ∈ L¹(ℝ³)` with compact support contained
in some ball `B(0,R)`, there exists `η > 0` and `𝓒` (depending only on `𝓡`and `R / a`) such that
as `ρ → 0⁺`,

`e ρ v ≥ 4πρ²a(1 + 128/(15√π)√(ρa³) - 𝓒(ρa³)^{1/2 + η})`.

Note: We (equivalently) take the limit as `ρ → 0⁺` rather than `ρa³ → 0⁺` as in the paper.

Note: While the wording of Theorem 1.2 in the paper suggests that `η` should also be allowed to
depend on `𝓡` and `R / a`, Theorem 6.8 makes it clear that `η` is in fact a universal constant.

Note: Since `v` is in `L¹(ℝ³)`, we interpret `v ≠ 0` to mean that `v` is not zero in `L¹(ℝ³)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Geometry.BoseGasesWanted](../../../../../sources/v2/WantedExt.md)
- S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean Via leanprover/lean-eval@38361be, problem `annals_bose_gases`.
