/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Mixed moments on the unit interval

Integrating the monomials `x ^ a * (1 - x) ^ b` gives the unnormalized Bernstein moments
of a finite measure. Splitting `1 = (1 - x) + x` yields the Pascal recurrence.
-/

@[expose] public section

namespace MeasureTheory

open unitInterval

/-- The mixed moment of `x` and its complement `1 - x` under a finite measure on `[0, 1]`. -/
noncomputable def unitIntervalMoment (μ : Measure I) [IsFiniteMeasure μ] (a b : ℕ) : ℝ :=
  ∫ x, (x : ℝ) ^ a * (1 - (x : ℝ)) ^ b ∂μ

/-- All mixed moments of the zero measure vanish. -/
@[simp] theorem unitIntervalMoment_zero_measure (a b : ℕ) :
    unitIntervalMoment (0 : Measure I) a b = 0 := by simp [unitIntervalMoment]

variable (μ : Measure I) [IsFiniteMeasure μ]

private theorem mixedPow_mem_unitInterval (a b : ℕ) (x : I) :
    0 ≤ (x : ℝ) ^ a * (1 - (x : ℝ)) ^ b ∧ (x : ℝ) ^ a * (1 - (x : ℝ)) ^ b ≤ 1 :=
  ⟨mul_nonneg (pow_nonneg (nonneg x) _) (pow_nonneg (one_sub_nonneg x) _),
    (mul_le_of_le_one_left (pow_nonneg (one_sub_nonneg x) _)
      (pow_le_one₀ (nonneg x) (le_one x))).trans
      (pow_le_one₀ (one_sub_nonneg x) (one_sub_le_one x))⟩

/-- Integrability of the mixed monomial on the unit interval. -/
theorem integrable_unitInterval_mixedPow (a b : ℕ) :
    Integrable (fun x : I => (x : ℝ) ^ a * (1 - (x : ℝ)) ^ b) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) (ae_of_all _ fun x => ?_)
  obtain ⟨h0, h1⟩ := mixedPow_mem_unitInterval a b x
  rwa [Real.norm_eq_abs, abs_of_nonneg h0]

/-- Mixed moments are nonnegative. -/
theorem unitIntervalMoment_nonneg (a b : ℕ) : 0 ≤ unitIntervalMoment μ a b :=
  integral_nonneg fun x => (mixedPow_mem_unitInterval a b x).1

/-- A mixed moment is at most the total mass. -/
theorem unitIntervalMoment_le_mass (a b : ℕ) : unitIntervalMoment μ a b ≤ μ.real Set.univ := by
  calc unitIntervalMoment μ a b ≤ ∫ _x, (1 : ℝ) ∂μ :=
        integral_mono (integrable_unitInterval_mixedPow μ a b) (integrable_const _) fun x =>
          (mixedPow_mem_unitInterval a b x).2
    _ = μ.real Set.univ := by simp

/-- Splitting the integrand using `1 = (1 - x) + x` gives two moments of the next degree. -/
theorem unitIntervalMoment_rec (a b : ℕ) :
    unitIntervalMoment μ a b = unitIntervalMoment μ a (b + 1) + unitIntervalMoment μ (a + 1) b := by
  unfold unitIntervalMoment
  rw [← integral_add (integrable_unitInterval_mixedPow μ _ _)
    (integrable_unitInterval_mixedPow μ _ _)]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

end MeasureTheory
