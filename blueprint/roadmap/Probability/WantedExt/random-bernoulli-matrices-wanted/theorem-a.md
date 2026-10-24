---
article_id: af_f090328d409d1a3b940974ec
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Probability.RandomBernoulliMatricesWanted.RandomBernoulliMatrices.theorem_A
---

# Theorem A

Statement of Theorem A:

For every `p ∈ (0, 1/2]` and `ε > 0` there exists `N, C > 0` such that for any `n ≥ N` and any
`n × n` random matrix `B` with mutually independent `Bernoulli(p)` entries,

`P(σ_min (B + sIIᵀ) ≤ t/√n) ≤ (1 - p + ε)ⁿ + Ct` for all `s ∈ [-1,0]` and `t > 0`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Probability.RandomBernoulliMatricesWanted](../../../../sources/v2/WantedExt.md)
- K. Tikhomirov, `Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-RandomBernoulliMatrices.lean Via leanprover/lean-eval@38361be, problem `annals_random_bernoulli_matrices`.
