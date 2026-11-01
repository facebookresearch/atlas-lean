---
article_id: af_064346dcd445c57f211b85fe
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Analysis.SupremumOfSelectorProcessesWanted.SupremumOfSelectorProcesses.theorem_1_2
---

# Theorem 1 2

Statement of Theorem 1.2:

There exists `L > 0` such that for any `0 < p < 1`, finite type `X`, and set `Λ` of functions from
`X` to `ℝ≥0` such that `0 < 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i] < ∞`, the collection of sets

`{s ⊆ X | sup_{f ∈ Λ} ∑ i ∈ s, f i ≥ L * 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i]}`

is `p-small`, where `Xp` is a binomial random subset of `X` with parameter `p`.

Note: The assumption `0 < 𝔼[sup_{f ∈ Λ} ∑ i ∈ Xp, f i] < ∞` is not explicitly stated in the theorem
but used in the last step of the proof where `𝔼 ≥ (L/L') * 𝔼` is a contradiction for `L > L'`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.SupremumOfSelectorProcessesWanted](../../../../../sources/v2/WantedExt.md)
- J. Park and H. T. Pham, `On a conjecture of Talagrand on selector processes and a consequence on positive empirical processes`, Annals of Math, 199 (3) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-3-SupremumOfSelectorProcesses.lean Via leanprover/lean-eval@38361be, problem `annals_supremum_of_selector_processes`.
