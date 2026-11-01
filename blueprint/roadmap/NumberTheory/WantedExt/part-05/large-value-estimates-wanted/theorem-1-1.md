---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.LargeValueEstimatesWanted.LargeValueEstimates.theorem_1_1
---

# Theorem 1 1

Statement of Theorem 1.1 (Large values estimate):

Suppose `(bₙ)` is a sequence of complex numbers with `|bₙ| ≤ 1`, and `(tᵣ)` for `r ≤ R` is a
sequence of `1`-separated points in `[0, T]` such that

`|∑_N^2N bₙ n^(itᵣ)| ≥ V`

for all `r ≤ R`. Then we have

`R ≤ T^(o(1)) * (N^2 V^(-2) + N^(18/5) V^(-4) + T N^(12/5) V^(-4))`.

Note: The inequality may be false at `T = 1`, so we must impose `T > 1`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.LargeValueEstimatesWanted](../../../../../sources/v2/WantedExt.md)
- L. Guth and J. Maynard, `New large value estimates for Dirichlet polynomials`, Annals of Math, 203 (2) 2026. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-2-LargeValueEstimates.lean Via leanprover/lean-eval@38361be, problem `annals_large_value_estimates`.
