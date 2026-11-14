/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.EwensInfiniteSites

/-!
# Tests for the infinite-sites sampling formula

Values of Tavaré's formula computed from its definition and checked against independent
computations: the geometric law for two genes, the convolution of two geometric laws for three
genes, the product `∏ k / (k + θ)` for `P(S = 0)`, and the point mass at `0` when `θ = 0`. Then
the theorems in the concrete marked Kingman model, so their hypotheses are not vacuous.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.EwensInfiniteSites

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- Two genes, `θ = 1`: `P(S_2 = 2) = 1 / 8`, the geometric mass `(1/2)^2 (1/2)`, computed from
the definition. -/
example : segSitesProb 1 2 2 = 1 / 8 := by
  norm_num [segSitesProb]

/-- Three genes, `θ = 1`: `P(S_3 = 1) = 2 (1/4 - 1/9) = 5/18`, computed from the definition. -/
example : segSitesProb 1 3 1 = 5 / 18 := by
  norm_num [segSitesProb, sum_range_succ]

/-- Independent check of the previous value: `S_3 = G_1 + G_2` with independent geometric
`G_k`, `P(G_k = a) = (k/(k+θ)) (θ/(k+θ))^a`. With `θ = 1`,
`P(S_3 = 1) = P(G_1 = 1) P(G_2 = 0) + P(G_1 = 0) P(G_2 = 1) = 5/18`. -/
example : (1 / 2 * (1 / 2 : ℝ)) * (2 / 3) + (1 / 2) * (2 / 3 * (1 / 3)) = 5 / 18 := by
  norm_num

/-- Three genes, `θ = 1`: `P(S_3 = 0) = 1/3`, from the definition, and the product
`∏_{k=1}^{2} k / (k + 1) = (1/2)(2/3)` evaluated directly. -/
example : segSitesProb 1 3 0 = 1 / 3 ∧
    ∏ k ∈ range (3 - 1), ((k : ℝ) + 1) / (k + 1 + 1) = 1 / 3 := by
  constructor <;> norm_num [segSitesProb, sum_range_succ, prod_range_succ]

/-- Zero mutation rate, four genes: `S_4 = 0` a.s., so the formula is the point mass at `0`
(`3 (1 - 2/2 + 1/3) = 1` and `0^1 = 0`), computed from the definition. -/
example : segSitesProb 0 4 0 = 1 ∧ segSitesProb 0 4 1 = 0 := by
  constructor <;> norm_num [segSitesProb, sum_range_succ, Nat.choose]

/-- The geometric law for two genes, through the general theorem. -/
example (θ : ℝ) : segSitesProb θ 2 0 = 1 / (θ + 1) := by
  simpa using segSitesProb_two θ 0

/-- The concrete model, two genes: `P(S_2 = m) = θ^m / (θ + 1)^{m+1}`. -/
example (θ : ℝ≥0) (m : ℕ) :
    (kingmanMutationMeasure 2 θ).real {p | ∑ b, p.2 b = m} = (θ : ℝ) ^ m / (θ + 1) ^ (m + 1) := by
  rw [measureReal_segSites_kingmanMutationMeasure θ le_rfl, segSitesProb_two]

/-- The concrete model, three genes, `θ = 1`: `P(S_3 = 1) = 5/18`. -/
example : (kingmanMutationMeasure 3 1).real {p | ∑ b, p.2 b = 1} = 5 / 18 := by
  rw [measureReal_segSites_kingmanMutationMeasure 1 (by norm_num)]
  norm_num [segSitesProb, sum_range_succ]

/-- The concrete model: at `s = 1` the generating function is the total mass `1`. -/
example (θ : ℝ≥0) (n : ℕ) :
    MathlibExt.Probability.pgf (fun p => ∑ b, p.2 b) (kingmanMutationMeasure n θ) 1 = 1 := by
  rw [pgf_segSites_kingmanMutationMeasure θ n (by simp)]
  simp only [sub_self, mul_zero, add_zero]
  exact prod_eq_one fun k _ => div_self (by positivity)

/-- The concrete model, three genes: no segregating sites with probability
`(1/(1+θ)) (2/(2+θ))`. -/
example (θ : ℝ≥0) :
    (kingmanMutationMeasure 3 θ).real {p | ∑ b, p.2 b = 0} =
      1 / (1 + θ) * (2 / (2 + θ)) := by
  rw [(KingmanTimes.ofMutationModel 3 θ).measureReal_segSites_eq_zero_of_mutation
    (hasCondDistrib_kingmanMutationMeasure 3 θ) (by norm_num)]
  simp only [show 3 - 1 = 2 from rfl, prod_range_succ, range_zero, prod_empty, one_mul,
    Nat.cast_zero, Nat.cast_one, zero_add]
  ring

/-- Tavaré's formula is a probability mass function. -/
example (θ : ℝ≥0) (m : ℕ) : 0 ≤ segSitesProb θ 5 m ∧ HasSum (segSitesProb θ 5) 1 :=
  ⟨segSitesProb_nonneg θ (by norm_num) m, hasSum_segSitesProb θ.coe_nonneg (by norm_num)⟩

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.EwensInfiniteSites
