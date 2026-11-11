/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Selection
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Selection
open scoped BigOperators

namespace MathlibExtTest.Biology.PopulationGenetics.Selection

/-! ### Haploid selection on two types (non-vacuity witness)

Frequencies `p = (1/2, 1/2)` and fitnesses `w = (1, 3)`: `w̄ = 2`, `p' = (1/4, 3/4)`,
`w̄' = 5/2`, `Var_p(w) = 1`, and indeed `w̄' - w̄ = 1/2 = Var_p(w) / w̄`. -/

/-- Frequencies of the two-type example. -/
noncomputable def p₂ : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Fitnesses of the two-type example. -/
noncomputable def w₂ : Fin 2 → ℝ := ![1, 3]

theorem meanFitness_p₂ : meanFitness p₂ w₂ = 2 := by
  norm_num [meanFitness, p₂, w₂, Fin.sum_univ_two]

example : select p₂ w₂ 0 = 1 / 4 ∧ select p₂ w₂ 1 = 3 / 4 := by
  simp only [select, meanFitness_p₂]
  norm_num [p₂, w₂]

example : meanFitness (select p₂ w₂) w₂ = 5 / 2 := by
  norm_num [meanFitness, select, meanFitness_p₂, p₂, w₂, Fin.sum_univ_two]

example : fitnessVariance p₂ w₂ = 1 := by
  simp only [fitnessVariance, meanFitness_p₂]
  norm_num [p₂, w₂, Fin.sum_univ_two]

/-- Fisher's theorem on the example. -/
example : meanFitness (select p₂ w₂) w₂ - meanFitness p₂ w₂ =
    fitnessVariance p₂ w₂ / meanFitness p₂ w₂ :=
  meanFitness_select_sub (by norm_num [p₂, Fin.sum_univ_two]) (by rw [meanFitness_p₂]; norm_num)

/-- Boundary case: equal fitnesses give zero variance and no change. -/
example : fitnessVariance p₂ (fun _ => 2) = 0 := by
  simp [fitnessVariance, meanFitness, p₂, Fin.sum_univ_two]
  norm_num

example (p w : Fin 3 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) (hw : ∀ i, 0 < w i) :
    meanFitness p w ≤ meanFitness (select p w) w ∧ ∑ i, select p w i = 1 ∧
      ∀ i, 0 ≤ select p w i :=
  ⟨meanFitness_le_meanFitness_select hp0 hp hw,
    sum_select (meanFitness_pos hp0 hp hw).ne', select_nonneg hp0 hp hw⟩

/-! ### Diploid viability selection: overdominance

Fitnesses `w AA = 1`, `w Aa = w aA = 2`, `w aa = 1` and `p = (1/2, 1/2)`: `w̄ = 3/2` and the
symmetric polymorphism is preserved, `p' = (1/2, 1/2)`. -/

/-- Overdominant genotype fitnesses. -/
noncomputable def wOver : Fin 2 → Fin 2 → ℝ := ![![1, 2], ![2, 1]]

example : diploidMeanFitness p₂ wOver = 3 / 2 := by
  norm_num [diploidMeanFitness, p₂, wOver, Fin.sum_univ_two]

example : diploidSelect p₂ wOver 0 = 1 / 2 := by
  norm_num [diploidSelect, marginalFitness, diploidMeanFitness, p₂, wOver, Fin.sum_univ_two]

/-- Symmetric fitnesses: the marginal fitness is the row marginal `∑ j, w i j * p j`. -/
example (i : Fin 2) : marginalFitness p₂ wOver i = ∑ j, wOver i j * p₂ j :=
  marginalFitness_of_symm (w := wOver) (by simp [Fin.forall_fin_two, wOver]) i

/-- Asymmetric ordered-genotype fitnesses `w₀₀ = w₀₁ = w₁₁ = 1`, `w₁₀ = 3` at `p = (1/2, 1/2)`:
both alleles of the favored genotype `(1, 0)` are transmitted, so the frequencies stay
`(1/2, 1/2)` (the row marginal alone would give `(1/3, 2/3)`). -/
noncomputable def wAsym : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![3, 1]]

example : diploidSelect p₂ wAsym 0 = 1 / 2 ∧ diploidSelect p₂ wAsym 1 = 1 / 2 := by
  norm_num [diploidSelect, marginalFitness, diploidMeanFitness, p₂, wAsym, Fin.sum_univ_two]

example (p : Fin 3 → ℝ) (w : Fin 3 → Fin 3 → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (hw : ∀ i j, 0 < w i j) : ∑ i, diploidSelect p w i = 1 ∧ ∀ i, 0 ≤ diploidSelect p w i :=
  ⟨sum_diploidSelect (diploidMeanFitness_pos hp0 hp hw).ne', diploidSelect_nonneg hp0 hp hw⟩

/-! ### The Price equation on three individuals

Fitnesses `w = (0, 1, 2)`, traits `z = (0, 1, 2)`, offspring traits `z' = z`: `w̄ = 1`,
`z̄ = 1`, `z̄' = 5/3`, `Cov(w, z) = 2/3`, `E[w Δz] = 0`. -/

/-- Fitnesses, trait values and offspring trait values `(0, 1, 2)` of the three individuals. -/
noncomputable def v₃ : Fin 3 → ℝ := ![0, 1, 2]

/-- Left side `w̄ (z̄' - z̄) = 1 * (5/3 - 1)`. -/
example : (𝔼 i, v₃ i) * ((∑ i, v₃ i * v₃ i) / ∑ i, v₃ i - 𝔼 i, v₃ i) = 2 / 3 := by
  simp only [Fintype.expect_eq_sum_div_card, Fin.sum_univ_three, v₃, Fintype.card_fin]
  norm_num

/-- Population covariance `Cov(w, z) = Var(z) = 2/3`. -/
example : (𝔼 i, (v₃ i - 𝔼 j, v₃ j) * (v₃ i - 𝔼 j, v₃ j)) = 2 / 3 := by
  simp only [Fintype.expect_eq_sum_div_card, Fin.sum_univ_three, v₃, Fintype.card_fin]
  norm_num

example (w z z' : Fin 3 → ℝ) (hw : ∑ i, w i ≠ 0) :
    (𝔼 i, w i) * ((∑ i, w i * z' i) / ∑ i, w i - 𝔼 i, z i) =
      (𝔼 i, (w i - 𝔼 j, w j) * (z i - 𝔼 j, z j)) + 𝔼 i, w i * (z' i - z i) :=
  price w z z' hw

/-- Outside the domain (`w̄ = 0`): `select` uses the junk value `x / 0 = 0`, so the frequencies
no longer sum to `1`; `sum_select` assumes `w̄ ≠ 0`. -/
example : ∑ i, select p₂ (fun _ => 0) i = 0 := by
  simp [select]

#print axioms meanFitness_select_sub
#print axioms price
#print axioms sum_diploidSelect

end MathlibExtTest.Biology.PopulationGenetics.Selection
