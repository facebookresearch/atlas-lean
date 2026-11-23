/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Bonferroni

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Bonferroni

/-- Three p-values `0.01, 0.02, 0.5`. -/
noncomputable def p3 : Fin 3 → ℝ := ![1 / 100, 2 / 100, 1 / 2]

/-- At `α = 0.05` the Bonferroni threshold is `α / 3 = 1 / 60`: only the first hypothesis is
rejected. -/
example : bonferroniRejections (1 / 20) p3 = {0} := by
  ext i
  fin_cases i <;> norm_num [bonferroniRejections, p3]

/-- Boundary: at `α = 0` nothing with a positive p-value is rejected. -/
example : bonferroniRejections 0 p3 = ∅ := by
  ext i
  fin_cases i <;> norm_num [bonferroniRejections, p3]

/-- The uniform law on `[0, 1]` is a probability measure. -/
instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Non-vacuity and no independence: all `m` p-values equal the same uniform variable
(perfectly dependent, all nulls true). Bonferroni still controls the FWER at `α`. -/
example (m : ℕ) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | (bonferroniRejections α (fun _ : Fin m => ω) ∩ Finset.univ).Nonempty} ≤
      ENNReal.ofReal α :=
  measure_bonferroni_familywiseError_le _ (fun _ => id) Finset.univ
    (fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id) hα₀ hα₁

/-- The Bonferroni inequality with `|H0| = 2` of `m = 3` hypotheses gives the bound `2α/3`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : Fin 3 → Ω → ℝ)
    (hnull : ∀ i ∈ ({1, 2} : Finset (Fin 3)), IsValidPValue μ (p i)) :
    μ {ω | ∃ i ∈ ({1, 2} : Finset (Fin 3)), p i ω ≤ 1 / 20 / 3} ≤
      ENNReal.ofReal (1 / 20 * 2 / 3) := by
  simpa using measure_exists_le_div_le μ p {1, 2} hnull (α := 1 / 20) (by norm_num)
    (by norm_num)

end MathlibExtTest.Probability.Statistics.MultipleTesting.Bonferroni
