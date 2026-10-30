/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Holm

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Holm

/-- Three p-values `0.01, 0.02, 0.5`. -/
noncomputable def p3 : Fin 3 → ℝ := ![1 / 100, 2 / 100, 1 / 2]

/-- At `α = 0.05`, Holm's steps are `p₍₁₎ = 0.01 ≤ α/3`, `p₍₂₎ = 0.02 ≤ α/2`, and
`p₍₃₎ = 0.5 > α`, so the step-down count is `2`. -/
theorem holmIndex_p3 : holmIndex (1 / 20) p3 = 2 := by
  have h60 : numBelow p3 ((1 / 20) / ((3 : ℕ) - (1 : ℕ) + 1)) = 1 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ (1 / 20) / ((3 : ℕ) - (1 : ℕ) + 1)) = {0} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have h40 : numBelow p3 ((1 / 20) / ((3 : ℕ) - (2 : ℕ) + 1)) = 2 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ (1 / 20) / ((3 : ℕ) - (2 : ℕ) + 1)) = {0, 1} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have h20 : numBelow p3 ((1 / 20) / ((3 : ℕ) - (3 : ℕ) + 1)) = 2 := by
    rw [numBelow, show (Finset.univ.filter fun i =>
      p3 i ≤ (1 / 20) / ((3 : ℕ) - (3 : ℕ) + 1)) = {0, 1} by
        ext i; fin_cases i <;> norm_num [p3]]
    rfl
  have hge : 2 ≤ holmIndex (1 / 20) p3 := by
    refine le_holmIndex (by norm_num) fun k hk => ?_
    rcases Finset.mem_Icc.1 hk with ⟨hk₁, hk₂⟩
    interval_cases k
    · rw [h60]
    · rw [h40]
  have hne : holmIndex (1 / 20) p3 ≠ 3 := by
    intro h3
    have := le_numBelow_of_le_holmIndex (α := 1 / 20) (p := p3) (k := 3) (by norm_num) h3.ge
    rw [h20] at this
    omega
  have hle := holmIndex_le (1 / 20) p3
  omega

/-- Holm rejects the two smallest p-values, whereas Bonferroni (threshold `α / 3`) rejects only
the first one here. -/
example : holmRejections (1 / 20) p3 = {0, 1} := by
  rw [holmRejections, holmIndex_p3]
  ext i
  fin_cases i <;> norm_num [p3]

example : (holmRejections (1 / 20) p3).card = holmIndex (1 / 20) p3 :=
  card_holmRejections (by norm_num) p3

/-- Boundary `α = 0`: the first step already fails, so nothing is rejected. -/
example : holmRejections 0 p3 = ∅ := by
  have h0 : holmIndex 0 p3 = 0 := by
    by_contra h
    have := le_numBelow_of_le_holmIndex (α := 0) (p := p3) (k := 1) le_rfl
      (Nat.one_le_iff_ne_zero.2 h)
    rw [zero_div, numBelow, Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i _ => by
      fin_cases i <;> norm_num [p3])] at this
    omega
  rw [holmRejections, h0]
  ext i
  fin_cases i <;> norm_num [p3]

/-- The uniform law on `[0, 1]` is a probability measure. -/
instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- Non-vacuity and no independence: all `m` p-values equal one uniform variable and every null
is true; Holm controls the FWER at `α`. -/
example (m : ℕ) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    volume.restrict (Set.Icc (0 : ℝ) 1)
      {ω | (holmRejections α (fun _ : Fin m => ω) ∩ Finset.univ).Nonempty} ≤
      ENNReal.ofReal α :=
  measure_holm_familywiseError_le _ (fun _ => id) Finset.univ
    (fun _ _ => isValidPValue_of_hasLaw_uniform HasLaw.id) hα₀ hα₁

end MathlibExtTest.Probability.Statistics.MultipleTesting.Holm
