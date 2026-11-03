/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.BenjaminiHochberg

/-- Three p-values `0.01, 0.02, 0.5`. -/
noncomputable def p3 : Fin 3 → ℝ := ![1 / 100, 2 / 100, 1 / 2]

/-- At `q = 0.1` the BH thresholds are `q k / 3 = 1/30, 1/15, 1/10`; two p-values are below
`1/15` but only two (not three) are below `1/10`, so the step-up index is `2`. -/
theorem bhIndex_p3 : bhIndex (1 / 10) p3 = 2 := by
  have h2 : numBelow p3 (1 / 10 * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 2 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ 1 / 10 * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = {0, 1} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have h3 : numBelow p3 (1 / 10 * ((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = 2 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ 1 / 10 * ((3 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = {0, 1} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have hge : 2 ≤ bhIndex (1 / 10) p3 := le_bhIndex (by norm_num) (by rw [h2])
  have hne : bhIndex (1 / 10) p3 ≠ 3 := by
    intro h
    have := bhIndex_le_numBelow (1 / 10) p3
    rw [h, h3] at this
    omega
  have hle := bhIndex_le (1 / 10) p3
  omega

/-- BH at `q = 0.1` rejects the two smallest p-values. -/
example : bhRejections (1 / 10) p3 = {0, 1} := by
  rw [bhRejections, bhIndex_p3]
  ext i
  fin_cases i <;> norm_num [p3]

example : (bhRejections (1 / 10) p3).card = 2 := by
  rw [card_bhRejections (by norm_num), bhIndex_p3]

/-- The uniform law on `[0, 1]` is a probability measure. -/
instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Non-vacuity: one uniform p-value with a true null satisfies every hypothesis of the BH
theorem, which then bounds the FDR by `q`. -/
example {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion Finset.univ (bhRejections q fun _ : Fin 1 => ω)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ q * (Finset.univ : Finset (Fin 1)).card / 1 := by
  simpa using integral_falseDiscoveryProportion_bhRejections_le
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ : Fin 1 => id) (fun _ => measurable_id)
    (iIndepFun.of_subsingleton) Finset.univ (fun _ _ => HasLaw.id) q hq₀ hq₁

end MathlibExtTest.Probability.Statistics.MultipleTesting.BenjaminiHochberg
