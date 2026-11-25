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

public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.AlgebraicDiagonal
public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.Completion
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import MathlibExt.Analysis.CStarAlgebra.Module.DirectSum.AlgebraicDiagonal.Bounded

/-!
# Uniformly bounded diagonals on completed module sums

For adjointable maps `T_i : E_i → F_i` of right pre-Hilbert modules, assume there is `c ≥ 0`
with `‖T_i‖ ≤ c` for every index. The coordinate map `(D_T x)_i = T_i x_i` on finite-support
sums extends to an adjointable map between their completed sums. Its adjoint has components
`T_i*`.

The formulas on finite-support images and component inclusions are preserved by completion.
Every nonnegative uniform component bound `c` satisfies `‖D_T‖ ≤ c`. The fibers may be
incomplete and the index type arbitrary or empty.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModule.DirectSum

universe uB uI uE uF

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {I : Type uI} {E : I → Type uE} {F : I → Type uF}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, SMul Bᵐᵒᵖ (E i)] [∀ i, CStarModule Bᵐᵒᵖ (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
  [∀ i, SMul Bᵐᵒᵖ (F i)] [∀ i, CStarModule Bᵐᵒᵖ (F i)]

/-- **Completed diagonal of a uniformly bounded family.** If `T_i : E_i → F_i` are adjointable and
admit one nonnegative common norm bound, their finite-support coordinate map extends to an
adjointable `Completed B E → Completed B F`. -/
@[expose]
def completedDiagonal
    (T : ∀ i, AdjointableOperator B (E i) (F i))
    (hBound : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ‖T i‖ ≤ c) :
    AdjointableOperator B (Completed B E) (Completed B F) := by
  let f0 : Algebraic B E →L[ℂ] Algebraic B F :=
    (algebraicDiagonal T).mkContinuousOfExistsBound (by
      rcases hBound with ⟨c, hc, hT⟩
      exact ⟨c, fun x ↦ algebraicDiagonal_norm_le T c hc hT x⟩)
  let g0 : Algebraic B F →L[ℂ] Algebraic B E :=
    (algebraicDiagonal (fun i ↦ (T i).adjointOperator)).mkContinuousOfExistsBound (by
      rcases hBound with ⟨c, hc, hT⟩
      have hAdjoint : ∀ i, ‖(T i).adjointOperator‖ ≤ c := by
        intro i
        simpa only [AdjointableOperator.norm_adjointOperator] using hT i
      exact ⟨c, fun y ↦ algebraicDiagonal_norm_le
        (fun i ↦ (T i).adjointOperator) c hc hAdjoint y⟩)
  have hPair : ∀ (x : Algebraic B E) (y : Algebraic B F),
      rightInner (B := B) (f0 x) y = rightInner (B := B) x (g0 y) := by
    intro x y
    change MulOpposite.unop
        (inner Bᵐᵒᵖ (algebraicDiagonal T x) y) =
      MulOpposite.unop
        (inner Bᵐᵒᵖ x
          (algebraicDiagonal (fun i ↦ (T i).adjointOperator) y))
    rw [inner_eq_algebraicInner, inner_eq_algebraicInner]
    exact congrArg MulOpposite.unop (algebraicDiagonal_adjoint_inner T x y)
  let algebraicOperator : AdjointableOperator B (Algebraic B E) (Algebraic B F) :=
    AdjointableOperator.ofAdjointPair f0 g0 hPair
  exact AdjointableOperator.completion algebraicOperator

/-- **Completed diagonal on finite-support images.** `completedDiagonal T hBound (x : Completed B
E) = (algebraicDiagonal T x : Completed B F)` for every algebraic vector `x`. -/
theorem completedDiagonal_apply_coe
    (T : ∀ i, AdjointableOperator B (E i) (F i))
    (hBound : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ‖T i‖ ≤ c) (x : Algebraic B E) :
    completedDiagonal T hBound (x : Completed B E) =
      (algebraicDiagonal T x : Completed B F) := by
  simp only [completedDiagonal, AdjointableOperator.completion_apply_coe,
    AdjointableOperator.ofAdjointPair_apply,
    LinearMap.mkContinuousOfExistsBound_apply]

/-- **Adjoint diagonal on finite-support images.** The adjoint of the completed diagonal sends the
completed image of `y` to the image of `algebraicDiagonal (fun i => (T i).adjointOperator) y`. -/
theorem completedDiagonal_adjoint_apply_coe
    (T : ∀ i, AdjointableOperator B (E i) (F i))
    (hBound : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ‖T i‖ ≤ c) (y : Algebraic B F) :
    (completedDiagonal T hBound).adjoint (y : Completed B F) =
      (algebraicDiagonal (fun i ↦ (T i).adjointOperator) y : Completed B E) := by
  simp only [completedDiagonal,
    AdjointableOperator.completion_adjoint_apply_coe,
    AdjointableOperator.ofAdjointPair_adjoint,
    LinearMap.mkContinuousOfExistsBound_apply]

/-- **Completed diagonal on a component inclusion.** `D_T (completedSingle i x) = completedSingle
i (T_i x)` in the target completed sum. -/
theorem completedDiagonal_apply_completedSingle
    (T : ∀ i, AdjointableOperator B (E i) (F i))
    (hBound : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ‖T i‖ ≤ c) (i : I) (x : E i) :
    completedDiagonal T hBound (completedSingle (B := B) (E := E) i x) =
      completedSingle (B := B) (E := F) i (T i x) := by
  rw [completedSingle_apply, completedDiagonal_apply_coe,
    single_apply_eq_singleLinear, algebraicDiagonal_singleLinear,
    completedSingle_apply, single_apply_eq_singleLinear]

/-- **Adjoint diagonal on a component inclusion.** `D_T* (completedSingle i y) = completedSingle i
(T_i* y)` in the source completed sum. -/
theorem completedDiagonal_adjoint_apply_completedSingle
    (T : ∀ i, AdjointableOperator B (E i) (F i))
    (hBound : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ‖T i‖ ≤ c) (i : I) (y : F i) :
    (completedDiagonal T hBound).adjoint (completedSingle (B := B) (E := F) i y) =
      completedSingle (B := B) (E := E) i ((T i).adjoint y) := by
  rw [completedSingle_apply, completedDiagonal_adjoint_apply_coe,
    single_apply_eq_singleLinear, algebraicDiagonal_singleLinear,
    AdjointableOperator.adjointOperator_apply,
    completedSingle_apply, single_apply_eq_singleLinear]

private theorem completedDiagonal_norm_apply_le
    (T : ∀ i, AdjointableOperator B (E i) (F i))
    (hBound : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ‖T i‖ ≤ c)
    (c : ℝ) (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c) (x : Completed B E) :
    ‖completedDiagonal T hBound x‖ ≤ c * ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (completedDiagonal T hBound).toContinuousLinearMap.continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro a
  rw [completedDiagonal_apply_coe, UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe]
  exact algebraicDiagonal_norm_le T c hc hT a

/-- **Every common bound controls the completed diagonal.** If `c ≥ 0` and `‖T_i‖ ≤ c` for all
indices, then `‖completedDiagonal T hBound‖ ≤ c`, independently of the particular existence
witness `hBound`. -/
theorem completedDiagonal_norm_le
    (T : ∀ i, AdjointableOperator B (E i) (F i))
    (hBound : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ‖T i‖ ≤ c)
    (c : ℝ) (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c) :
    ‖completedDiagonal T hBound‖ ≤ c := by
  rw [AdjointableOperator.norm_eq]
  exact ContinuousLinearMap.opNorm_le_bound _ hc
    (completedDiagonal_norm_apply_le T hBound c hc hT)

end CStarModule.DirectSum
