---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted.FractionalExpectationThresholds.theorem_1_1
---

# Theorem 1 1

Statement of Theorem 1.1:

There exists a universal constant `K` such that for any finite set `X` and any increasing
collection of sets `𝓕` such that `l(𝓕)` is at least `2`,

`p_c(𝓕) ≤ K * q_f(𝓕) * log l(𝓕)`.

Note: The assumption that `l(𝓕)` is at least `2` is not explicitly in the paper but is needed
because if `l(𝓕) = 1` then `Real.log (l 𝓕) = 0`, but `p_c 𝓕 ∈ (0,1)` (so the inequality clearly
cannot hold).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.FractionalExpectationThresholdsWanted](../../../../../sources/v2/WantedExt.md)
- K. Frankston, J. Kahn, B. Narayanan, and J. Park, `Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-FractionalExpectationThresholds.lean Via leanprover/lean-eval@38361be, problem `annals_fractional_expectation_thresholds`.
