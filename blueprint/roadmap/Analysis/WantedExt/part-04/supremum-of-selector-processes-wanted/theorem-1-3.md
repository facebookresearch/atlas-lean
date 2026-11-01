---
article_id: af_44fd082ab82cf3b8c1b9aa84
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Analysis.SupremumOfSelectorProcessesWanted.SupremumOfSelectorProcesses.theorem_1_3
---

# Theorem 1 3

Statement of Theorem 1.3:

There exists `L > 0` such that for any `N > 0`, i.i.d random variables `Y_1, …, Y_N` distributed
according to a Borel probability measure `ν` on a Polish space `𝕋`, if `𝓕` is a finite set of
non-negative functions in `L∞(𝕋)` and `0 < 𝔼[sup_{f ∈ 𝓕} Z Y f] < ∞` then there exists a finite
collection `𝓒` of pairs `(g, t)` where `g : 𝕋 → ℝ≥0`, `t > 0` such that

`{sup_{f ∈ 𝓕} Z N Y f ≥ L * 𝔼[sup_{f ∈ 𝓕} Z N Y f] } ⊆ ⋃ (g,t) ∈ 𝓒, {t ≤ Z N Y g}`

and

`∑ (g,t) ∈ 𝓒, P(t ≤ Z N Y g) ≤ 2⁻¹`.

Note: The requirement that the collection `𝓒` be finite is not explicitly stated in the paper.
However, `𝓒` must at least be assumed to be countable in order for the sum to make sense,
and the collections `𝓒` produced by the proof are indeed finite.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Analysis.SupremumOfSelectorProcessesWanted](../../../../../sources/v2/WantedExt.md)
- J. Park and H. T. Pham, `On a conjecture of Talagrand on selector processes and a consequence on positive empirical processes`, Annals of Math, 199 (3) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-3-SupremumOfSelectorProcesses.lean Via leanprover/lean-eval@38361be, problem `annals_supremum_of_selector_processes`.
