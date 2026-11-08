/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Actual sign-matrix and conference-matrix inputs
-/
module

public import MathlibExt.LinearAlgebra.Matrix.SignConditionNumberDecay

@[expose] public section

open Matrix.SignConditionNumber

namespace MathlibExtTest.LinearAlgebra.Matrix.SignConditionNumber

theorem actual_sign_order_one : ∃ A : SignMatrix 1, A.realize = (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
    conditionNumber A.realize = 1 ∧ minimumConditionNumber ⟨1, Nat.zero_lt_one⟩ = 1 := by
  let A : SignMatrix 1 := fun _ _ => false
  have hr : A.realize = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [A, SignMatrix.realize, Matrix.one_apply, Subsingleton.elim i j]
  refine ⟨A, hr, ?_, minimumConditionNumber_one⟩
  rw [hr, conditionNumber_one_order_one]

theorem actual_minimum_order_one_finite : minimumConditionNumber ⟨1, Nat.zero_lt_one⟩ < ⊤ := by
  rw [minimumConditionNumber_one]
  exact ENNReal.one_lt_top

theorem actual_minimum_attained (n : {n : ℕ // 0 < n}) :
    ∃ A : SignMatrix n.1, minimumConditionNumber n = conditionNumber A.realize :=
  minimumConditionNumber_attained n

theorem actual_zero_order_two_singular : conditionNumber (0 : Matrix (Fin 2) (Fin 2) ℝ) = ⊤ :=
  conditionNumber_zero 2

theorem actual_empty_order_singular : conditionNumber (0 : Matrix (Fin 0) (Fin 0) ℝ) = ⊤ :=
  conditionNumber_zero 0

theorem not_conference_order_one : ¬ IsSymmetricConference (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro h
  have := h.1
  omega

theorem actual_conference_order_two :
    IsSymmetricConference (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply]
  · intro i
    fin_cases i <;> norm_num
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem actual_conference_add_one_sign_matrix : ∃ A : SignMatrix 2,
    A.realize = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) + 1 := by
  exact IsSymmetricConference.exists_realize_add_one actual_conference_order_two

theorem actual_conference_add_one_condition_top :
    conditionNumber ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) + 1) = ⊤ := by
  let T := Matrix.toEuclideanLin ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) + 1)
  apply conditionNumber_eq_top_of_smallest_eq_zero
  change T.singularValues 1 = 0
  by_contra h
  have hpos := (T.singularValues_pos_iff_ne_zero 1).mpr h
  have hi : Function.Injective T := T.injective_iff_forall_lt_finrank_singularValues_pos.mpr
    (by
      intro i hi
      have hi1 : i ≤ 1 := by simpa using hi
      exact lt_of_lt_of_le hpos (T.singularValues_antitone hi1))
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, -1]
  have hTv : T v = T 0 := by
    ext i
    fin_cases i <;>
      norm_num [T, v, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hv := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) (hi hTv)
  norm_num [v] at hv

theorem conference_order_two_ratio_top :
    ENNReal.ofReal (Real.sqrt ((2 : ℝ) - 1) + 1) /
      ENNReal.ofReal (Real.sqrt ((2 : ℝ) - 1) - 1) = ⊤ := by
  norm_num [ENNReal.div_zero]

theorem separate_unconditional_and_conditional_endpoints :
    ¬ (((1 : ℝ) / 4 : ℝ) : EReal) ≤ (((17 : ℝ) / 92 : ℝ) : EReal) := by
  norm_num

end MathlibExtTest.LinearAlgebra.Matrix.SignConditionNumber
