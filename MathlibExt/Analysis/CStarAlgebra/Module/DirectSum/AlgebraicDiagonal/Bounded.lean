/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.AlgebraicDiagonal
import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.Completion
import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.GramBound
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Finite coefficient bounds for algebraic diagonals

A uniformly bounded given rectangular family satisfies the genuine coefficient
Gram bound and norm bound on the actual algebraic direct sum. Component
completion is used only in proofs; the original fibers may be incomplete.

The fixed source support is used even when the diagonal kills coordinates.
The numeric bound changes no operator value. No scalar sum of squared fiber
norms, continuous/completed diagonal, compactness or action is asserted.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators CStarAlgebra RightActions

namespace CStarModule.DirectSum

universe uB uI uE uF

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {I : Type uI} {E : I → Type uE} {F : I → Type uF}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
  [∀ i, SMul Bᵐᵒᵖ (F i)] [∀ i, CStarModule Bᵐᵒᵖ (F i)]

attribute [local instance] CStarModule.completionCStarModule

omit [StarOrderedRing Bᵐᵒᵖ] in
private theorem gram_smul_nonneg (i : I) (x : E i) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ r • inner Bᵐᵒᵖ x x := by
  have h := CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (E := E i)
    (x := Real.sqrt r • x)
  rw [CStarModule.inner_smul_left_real, CStarModule.inner_smul_right_real,
    smul_smul, Real.mul_self_sqrt hr] at h
  exact h

private theorem component_gram_bound (i : I)
    (T : AdjointableOperator B (E i) (F i)) (c : ℝ) (hT : ‖T‖ ≤ c) (x : E i) :
    inner Bᵐᵒᵖ (T x) (T x) ≤ (c ^ 2 : ℝ) • inner Bᵐᵒᵖ x x := by
  have hGram : inner Bᵐᵒᵖ (T x) (T x) ≤
      (‖T.completion‖ ^ 2 : ℝ) • inner Bᵐᵒᵖ x x := by
    simpa only [AdjointableOperator.completion_apply_coe,
      CStarModule.completionCStarModule_inner_coe_coe] using
      (T.completion.inner_apply_self_le_norm_sq_smul
        (x : UniformSpace.Completion (E i)))
  have hNorm : ‖T.completion‖ ≤ c := T.completion_norm_le.trans hT
  have hSquare : ‖T.completion‖ ^ 2 ≤ c ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self (_root_.norm_nonneg T.completion) hNorm
  have hRemainder : 0 ≤
      ((c ^ 2 - ‖T.completion‖ ^ 2 : ℝ) • inner Bᵐᵒᵖ x x) :=
    gram_smul_nonneg i x _ (sub_nonneg.mpr hSquare)
  have hDifference : 0 ≤ (c ^ 2 : ℝ) • inner Bᵐᵒᵖ x x -
      (‖T.completion‖ ^ 2 : ℝ) • inner Bᵐᵒᵖ x x := by
    simpa only [sub_smul] using hRemainder
  exact hGram.trans (sub_nonneg.mp hDifference)

omit [StarOrderedRing Bᵐᵒᵖ] in
private theorem diagonal_inner_fixed_support
    (T : ∀ i, AdjointableOperator B (E i) (F i)) (x : Algebraic B E) :
    algebraicInner (algebraicDiagonal T x) (algebraicDiagonal T x) =
      ∑ i ∈ support x, inner Bᵐᵒᵖ (T i (toDFinsupp x i)) (T i (toDFinsupp x i)) := by
  classical
  rw [algebraicInner_eq_sum]
  simp_rw [algebraicDiagonal_apply]
  refine Finset.sum_subset (support_algebraicDiagonal_subset T x) ?_
  intro i _hi hni
  have hz := (not_mem_support_iff (algebraicDiagonal T x) i).mp hni
  rw [algebraicDiagonal_apply] at hz
  rw [hz]
  exact CStarModule.inner_zero_left

/-- The actual finite coefficient Gram bound over the unchanged source support.
The original source and target component modules need not be complete. -/
theorem algebraicDiagonal_inner_self_le
    (T : ∀ i, AdjointableOperator B (E i) (F i)) (c : ℝ)
    (hBound : ∀ i, ‖T i‖ ≤ c) (x : Algebraic B E) :
    algebraicInner (algebraicDiagonal T x) (algebraicDiagonal T x) ≤
      (c ^ 2 : ℝ) • algebraicInner x x := by
  classical
  calc
    algebraicInner (algebraicDiagonal T x) (algebraicDiagonal T x) =
        ∑ i ∈ support x,
          inner Bᵐᵒᵖ (T i (toDFinsupp x i)) (T i (toDFinsupp x i)) :=
      diagonal_inner_fixed_support T x
    _ ≤ ∑ i ∈ support x, (c ^ 2 : ℝ) •
        inner Bᵐᵒᵖ (toDFinsupp x i) (toDFinsupp x i) :=
      Finset.sum_le_sum fun i _hi ↦ component_gram_bound i (T i) c (hBound i) _
    _ = (c ^ 2 : ℝ) • algebraicInner x x := by
      rw [algebraicInner_eq_sum, Finset.smul_sum]

/-- A given nonnegative uniform operator bound bounds the actual algebraic
diagonal norm, with no original fiber completeness or nonempty-index premise. -/
theorem algebraicDiagonal_norm_le
    (T : ∀ i, AdjointableOperator B (E i) (F i)) (c : ℝ) (hc : 0 ≤ c)
    (hBound : ∀ i, ‖T i‖ ≤ c) (x : Algebraic B E) :
    ‖algebraicDiagonal T x‖ ≤ c * ‖x‖ := by
  have hPositive : 0 ≤
      algebraicInner (algebraicDiagonal T x) (algebraicDiagonal T x) := by
    rw [algebraicInner_eq_sum]
    exact Finset.sum_nonneg fun i _hi ↦ CStarModule.inner_self_nonneg
  have hCoefficient := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (algebraicDiagonal_inner_self_le T c hBound x) hPositive
  have hScaledNorm : ‖(c ^ 2 : ℝ) • algebraicInner x x‖ =
      c ^ 2 * ‖algebraicInner x x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg c)]
  have hCoefficientNorm : ‖algebraicInner (algebraicDiagonal T x)
      (algebraicDiagonal T x)‖ ≤ c ^ 2 * ‖algebraicInner x x‖ :=
    hCoefficient.trans_eq hScaledNorm
  calc
    ‖algebraicDiagonal T x‖ =
        Real.sqrt ‖algebraicInner (algebraicDiagonal T x)
          (algebraicDiagonal T x)‖ := norm_algebraic _
    _ ≤ Real.sqrt (c ^ 2 * ‖algebraicInner x x‖) :=
      Real.sqrt_le_sqrt hCoefficientNorm
    _ = c * ‖x‖ := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc, ← norm_algebraic x]

end CStarModule.DirectSum
