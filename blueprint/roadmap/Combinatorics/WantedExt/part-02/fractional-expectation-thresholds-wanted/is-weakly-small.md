---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.FractionalExpectationThresholdsWanted.FractionalExpectationThresholds.IsWeaklySmall
---

# Is Weakly Small

We say that a collection `𝓕` of subsets of `X` is `weakly p-small` if there exists
`g : Set X → ℝ≥0` such that `∀ T ∈ 𝓕, ∑ S ⊆ T, g(S) ≥ 1` and `∑ S ⊆ X, g(S) p^|S| ≤ 1/2`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.FractionalExpectationThresholdsWanted](../../../../../sources/v2/WantedExt.md)
