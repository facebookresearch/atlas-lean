/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.UCB1.PullCountBound

/-!
# Pull-count bound tests

The bounds applied to deterministic rewards on a one-point probability space, where every family
of random variables is independent: arm `0` always pays `1`, arm `1` always pays `0`, and the
least-index run, or any run in the lower-integral form, plays arm `1` at most
`8 ln n + 1 + π² / 3` times among its first `n` plays.
-/

namespace Cslib.MachineLearning.UCB1

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- On a one-point space every family of random variables is independent. -/
private lemma iIndepFun_unit {ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (f : ∀ i, Unit → β i) : iIndepFun f (Measure.dirac ()) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  classical
  simp only [Measure.dirac_apply]
  simp only [Set.indicator_apply, Set.mem_iInter₂, Set.mem_preimage, Pi.one_apply]
  rw [Finset.prod_boole]

/-- Deterministic rewards: arm `0` always pays `1` and arm `1` always pays `0`. -/
private noncomputable def r : Fin 2 → ℝ := ![1, 0]

private lemma iSup_integral_dirac_r : (⨆ j, ∫ s, s ∂(Measure.dirac (r j))) = 1 := by
  simp only [integral_dirac]
  refine le_antisymm (ciSup_le fun j ↦ ?_) (le_ciSup_of_le (Set.finite_range _).bddAbove 0 ?_)
  · fin_cases j <;> simp [r]
  · simp [r]

-- The bound in expectation for deterministic rewards: the least-index run plays the arm of gap
-- `1` at most `8 ln n + 1 + π² / 3` times among its first `n` plays.
example (n : ℕ) :
    (Nat.count (ucb1Arm (fun j _ ↦ r j) · = 1) n : ℝ) ≤ 8 * log n + 1 + π ^ 2 / 3 := by
  have h := integral_count_le (P := Measure.dirac ()) (X := fun j _ _ ↦ r j)
    (ν := fun j ↦ Measure.dirac (r j)) (fun _ _ ↦ measurable_const) (iIndepFun_unit _)
    (fun j _ ↦ by simp) (fun j ↦ by fin_cases j <;> simp [r])
    (fun _ ↦ isUCB1Run_ucb1Arm _) (fun _ ↦ measurable_const) (i := 1)
    (by rw [iSup_integral_dirac_r]; simp [integral_dirac, r]) n
  rw [iSup_integral_dirac_r] at h
  simpa [integral_dirac, r] using h

-- The lower-integral form holds for every run, here any run on these rewards.
example (A : Unit → ℕ → Fin 2) (hA : ∀ ω, IsUCB1Run (fun j _ ↦ r j) (A ω)) (n : ℕ) :
    (Nat.count (A () · = 1) n : ℝ≥0∞) ≤ ENNReal.ofReal (8 * log n + 1 + π ^ 2 / 3) := by
  have h := lintegral_count_le (P := Measure.dirac ()) (X := fun j _ _ ↦ r j)
    (ν := fun j ↦ Measure.dirac (r j)) (fun _ _ ↦ measurable_const) (iIndepFun_unit _)
    (fun j _ ↦ by simp) (fun j ↦ by fin_cases j <;> simp [r]) hA (i := 1)
    (by rw [iSup_integral_dirac_r]; simp [integral_dirac, r]) n
  rw [iSup_integral_dirac_r] at h
  simpa [lintegral_dirac, integral_dirac, r] using h

end Cslib.MachineLearning.UCB1
