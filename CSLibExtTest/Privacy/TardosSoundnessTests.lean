/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.TardosSoundness

/-!
# Tardos fixed-bias soundness tests

Numeric checks of the Tardos weight moments, the one-column exponential moment
in the regime the source's stated range misses, and a nonvacuous instance of
the fixed-bias soundness bound with Tardos's constants at `c = 1`.
-/

@[expose] public section

namespace CSLibExtTest.Privacy.TardosSoundnessTests

open CSLibExt.Privacy.Fingerprinting
open scoped ENNReal

/-- The bias `1 / 2`. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp]
theorem half_val : (half : ℝ) = 1 / 2 := rfl

theorem tardosWeight_quarter_true : tardosWeight (1 / 4) true = Real.sqrt 3 := by
  rw [tardosWeight_true]
  norm_num

theorem tardosWeight_quarter_false : tardosWeight (1 / 4) false = -Real.sqrt (1 / 3) := by
  rw [tardosWeight_false]
  norm_num

/-- Mean zero at the asymmetric bias `1 / 4`: `(1/4) √3 - (3/4) √(1/3) = 0`. -/
theorem quarter_mean :
    (1 / 4 : ℝ) * Real.sqrt 3 + (1 - 1 / 4) * -Real.sqrt (1 / 3) = 0 := by
  rw [← tardosWeight_quarter_true, ← tardosWeight_quarter_false]
  exact tardosWeight_mean_eq_zero (by norm_num) (by norm_num)

/-- Second moment one at `1 / 4`: `(1/4) 3 + (3/4) (1/3) = 1`. -/
theorem quarter_sq_mean :
    (1 / 4 : ℝ) * Real.sqrt 3 ^ 2 + (1 - 1 / 4) * (-Real.sqrt (1 / 3)) ^ 2 = 1 := by
  rw [← tardosWeight_quarter_true, ← tardosWeight_quarter_false]
  exact tardosWeight_sq_mean_eq_one (by norm_num) (by norm_num)

/-- At Tardos's `c = 1` constants (`p = t = 1 / 300`, `α = 1 / 10`) the scaled
positive weight `√299 / 10` exceeds the source's stated range `u < 1.7`. -/
theorem scaled_weight_c1_gt :
    (17 / 10 : ℝ) < 1 / 10 * tardosWeight (1 / 300) true := by
  rw [tardosWeight_true]
  have h : (1 - 1 / 300 : ℝ) / (1 / 300) = 299 := by norm_num
  rw [h]
  have h17 : (17 : ℝ) = Real.sqrt (17 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  have hlt : Real.sqrt (17 ^ 2) < Real.sqrt 299 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- The one-column exponential moment bound still holds there. -/
theorem exp_mean_c1 :
    (1 / 300 : ℝ) * Real.exp (1 / 10 * tardosWeight (1 / 300) true) +
        (1 - 1 / 300) * Real.exp (1 / 10 * tardosWeight (1 / 300) false) ≤
      1 + (1 / 10) ^ 2 :=
  tardosWeight_exp_mean_le (by norm_num) (by norm_num) (by norm_num)

/-- Tardos's constants at `c = 1`, `ε = 1 / 2`, `k = 1`: length `100`,
threshold `20`, three users and the all-ones word. -/
theorem tardos_c1_instance :
    ((biasCodebookPMF (n := 3) (fun _ : Fin 100 => half)).toOuterMeasure
        {C | TardosAccuses (fun _ => (half : ℝ)) (20 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) C
          (fun _ => true) 0}).toReal < 1 / 2 := by
  refine tardos_soundness_fixed_bias (n := 3) (c := 1) (k := 1) le_rfl (by norm_num)
    (by norm_num) ?_ (by norm_num) _ (fun _ => by norm_num) _ _
  have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
  norm_num at h ⊢
  linarith

/-- The event in `tardos_c1_instance` has positive probability: the all-true
codebook has score `100 > 20` for user `0`. -/
theorem tardos_c1_instance_pos :
    0 < ((biasCodebookPMF (n := 3) (fun _ : Fin 100 => half)).toOuterMeasure
        {C | TardosAccuses (fun _ => (half : ℝ)) (20 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) C
          (fun _ => true) 0}).toReal := by
  apply ENNReal.toReal_pos
  · rw [Ne, PMF.toOuterMeasure_apply_eq_zero_iff, Set.not_disjoint_iff]
    refine ⟨fun _ _ => true, ?_, ?_⟩
    · rw [PMF.mem_support_iff, biasCodebookPMF_apply]
      simp [bernoulliMass]
    · show (20 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) <
        ∑ _j : Fin 100, (if true = true then tardosWeight (half : ℝ) true else 0)
      have hw : tardosWeight (half : ℝ) true = 1 := by
        rw [half_val, tardosWeight_true]
        norm_num
      rw [ite_eq_left rfl, hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _

#print axioms tardosWeight_mean_eq_zero
#print axioms tardosWeight_sq_mean_eq_one
#print axioms tardosWeight_exp_mean_le
#print axioms sum_biasCodebookPMF_mul_exp_tardosScore
#print axioms tardosAccuses_prob_le
#print axioms tardos_soundness_fixed_bias
#print axioms tardos_c1_instance
#print axioms tardos_c1_instance_pos

end CSLibExtTest.Privacy.TardosSoundnessTests
