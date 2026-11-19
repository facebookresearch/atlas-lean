/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Classical.MultilevelPrice
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators
open MathlibExt.Biology.PopulationGenetics.Classical.MultilevelPrice

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.MultilevelPrice

/-- Two groups, each with two individuals. -/
abbrev groupType : Fin 2 → Type := fun _ => Fin 2

/-- Fitness-like values `[[1, 3], [2, 6]]` on the two groups. -/
noncomputable def xEx : (Σ k, groupType k) → ℝ := fun i => ![![1, 3], ![2, 6]] i.1 i.2

/-- Trait-like values `[[2, 1], [5, 4]]` on the two groups. -/
noncomputable def yEx : (Σ k, groupType k) → ℝ := fun i => ![![2, 1], ![5, 4]] i.1 i.2

/-- Equal group sizes give each group weight `1 / 2`. -/
noncomputable def qEx : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Group means of `xEx`: `(2, 4)`. -/
noncomputable def XEx : Fin 2 → ℝ := ![2, 4]

/-- Group means of `yEx`: `(3 / 2, 9 / 2)`. -/
noncomputable def YEx : Fin 2 → ℝ := ![3 / 2, 9 / 2]

theorem hqEx : ∀ k, qEx k =
    (Fintype.card (groupType k) : ℝ) / Fintype.card (Σ k, groupType k) := by
  intro k
  fin_cases k <;> norm_num [groupType, qEx, Fintype.card_sigma]

theorem hXEx : ∀ k, XEx k = 𝔼 j, xEx ⟨k, j⟩ := by
  intro k
  fin_cases k <;>
    norm_num [groupType, XEx, xEx, Fintype.expect_eq_sum_div_card, Fin.sum_univ_two]

theorem hYEx : ∀ k, YEx k = 𝔼 j, yEx ⟨k, j⟩ := by
  intro k
  fin_cases k <;>
    norm_num [groupType, YEx, yEx, Fintype.expect_eq_sum_div_card, Fin.sum_univ_two]

/-- Concrete law of total covariance: the total covariance is `3 / 4`, split
as between-group `3 / 2` plus within-group `-3 / 4`. -/
example :
    𝔼 i, (xEx i - 𝔼 j, xEx j) * (yEx i - 𝔼 j, yEx j) = 3 / 2 + (-3 / 4 : ℝ) := by
  have h := cov_eq_between_add_within xEx yEx qEx XEx YEx hqEx hXEx hYEx
  rw [h]
  norm_num [qEx, XEx, YEx, xEx, yEx, groupType, Fintype.expect_eq_sum_div_card,
    Fintype.sum_sigma, Fin.sum_univ_two]

/-- With `z' = z`, the concrete multilevel Price equation has total change
term `3 / 4`: mean fitness `3`, offspring mean trait `13 / 4`, and trait mean
`3`. -/
example :
    (𝔼 i, xEx i) * ((∑ i, xEx i * yEx i) / ∑ i, xEx i - 𝔼 i, yEx i) = 3 / 4 := by
  have h := multilevel_price xEx yEx yEx qEx XEx YEx hqEx hXEx hYEx (by
    norm_num [xEx, groupType, Fintype.sum_sigma, Fin.sum_univ_two])
  rw [h]
  norm_num [qEx, XEx, YEx, xEx, yEx, groupType, Fintype.expect_eq_sum_div_card,
    Fintype.sum_sigma, Fin.sum_univ_two]

end MathlibExtTest.Biology.PopulationGenetics.Classical.MultilevelPrice
