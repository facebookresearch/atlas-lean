/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.DiploidSelection
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Selection
open scoped BigOperators

namespace MathlibExtTest.Biology.PopulationGenetics.DiploidSelection

/-! ### Overdominance on two alleles (non-vacuity witness)

Genotype fitnesses `w₀₀ = w₁₁ = 1`, `w₀₁ = w₁₀ = 2` (heterozygote advantage) and allele
frequencies `p = (1/4, 3/4)`: marginal fitnesses `m = (7/4, 5/4)`, `w̄ = 11/8`,
`p' = (7/22, 15/22)`, `w̄' = 347/242 > 11/8`. Wright's formula: `Δx = 3/44`, `dw̄/dx = 1`. -/

/-- Overdominant genotype fitnesses. -/
noncomputable def wO : Fin 2 → Fin 2 → ℝ := ![![1, 2], ![2, 1]]

/-- Allele frequencies of the example. -/
noncomputable def pO : Fin 2 → ℝ := ![1 / 4, 3 / 4]

theorem diploidMeanFitness_pO : diploidMeanFitness pO wO = 11 / 8 := by
  norm_num [diploidMeanFitness, pO, wO, Fin.sum_univ_two]

theorem diploidSelect_pO_zero : diploidSelect pO wO 0 = 7 / 22 := by
  rw [diploidSelect, diploidMeanFitness_pO]
  norm_num [marginalFitness, pO, wO, Fin.sum_univ_two]

theorem pO_nonneg : ∀ i, 0 ≤ pO i := by
  intro i; fin_cases i <;> norm_num [pO]

theorem sum_pO : ∑ i, pO i = 1 := by norm_num [pO, Fin.sum_univ_two]

theorem wO_nonneg : ∀ i j, 0 ≤ wO i j := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [wO]

/-- The hypotheses of the theorems are satisfiable and the inequality is strict here. -/
example : diploidMeanFitness pO wO < diploidMeanFitness (diploidSelect pO wO) wO := by
  refine diploidMeanFitness_lt_diploidMeanFitness_diploidSelect pO_nonneg sum_pO wO_nonneg
    (by rw [diploidMeanFitness_pO]; norm_num) fun h => ?_
  have h0 := congrFun h 0
  rw [diploidSelect_pO_zero] at h0
  norm_num [pO] at h0

/-- The new mean fitness, computed directly: `347/242`. -/
example : diploidMeanFitness (diploidSelect pO wO) wO = 347 / 242 := by
  have h1 : diploidSelect pO wO 1 = 15 / 22 := by
    rw [diploidSelect, diploidMeanFitness_pO]
    norm_num [marginalFitness, pO, wO, Fin.sum_univ_two]
  simp only [diploidMeanFitness, Fin.sum_univ_two, diploidSelect_pO_zero, h1]
  norm_num [wO]

/-- Wright's formula at `x = 1/4`: `dw̄/dx = 1`. -/
example : deriv (fun y => diploidMeanFitness ![y, 1 - y] wO) (1 / 4) = 1 := by
  rw [(hasDerivAt_diploidMeanFitness_two wO (1 / 4)).deriv]
  norm_num [marginalFitness, wO, Fin.sum_univ_two]

/-- Wright's formula at `x = 1/4`: `Δx = x (1 - x) (dw̄/dx) / (2 w̄) = 3/44`. -/
example : diploidSelect ![1 / 4, 1 - 1 / 4] wO 0 - 1 / 4 = 3 / 44 := by
  have hw : diploidMeanFitness ![(1 : ℝ) / 4, 1 - 1 / 4] wO = 11 / 8 := by
    norm_num [diploidMeanFitness, wO, Fin.sum_univ_two]
  rw [diploidSelect_two_sub wO (1 / 4) (by rw [hw]; norm_num), hw,
    (hasDerivAt_diploidMeanFitness_two wO (1 / 4)).deriv]
  norm_num [marginalFitness, wO, Fin.sum_univ_two]

/-! ### Boundary cases -/

/-- The polymorphic equilibrium `p = (1/2, 1/2)` of the overdominant model is a fixed point, so
mean fitness is unchanged there (the equality case). -/
example : diploidMeanFitness (diploidSelect ![1 / 2, 1 / 2] wO) wO =
    diploidMeanFitness ![1 / 2, 1 / 2] wO := by
  have hfix : diploidSelect ![(1 : ℝ) / 2, 1 / 2] wO = ![1 / 2, 1 / 2] := by
    funext i
    fin_cases i <;>
      norm_num [diploidSelect, marginalFitness, diploidMeanFitness, wO, Fin.sum_univ_two]
  rw [hfix]

/-- A fixed allele (`p = (1, 0)`) stays fixed: alleles absent before selection stay absent. -/
example : diploidSelect ![1, 0] wO 1 = 0 := by
  norm_num [diploidSelect]

/-- Junk value outside the domain: with zero mean fitness (`w = 0`) the selection map divides by
zero and returns `0`, which is not a frequency vector. The theorems assume `0 < w̄`. -/
example : diploidSelect pO (fun _ _ => 0) 0 = 0 := by
  simp [diploidSelect, diploidMeanFitness]

end MathlibExtTest.Biology.PopulationGenetics.DiploidSelection
