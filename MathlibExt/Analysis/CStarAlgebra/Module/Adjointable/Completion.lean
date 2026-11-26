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

public import MathlibExt.Analysis.CStarAlgebra.Module.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.OfPair

/-!
# Completing adjointable maps of right modules

For right pre-Hilbert `B`-modules `E,F` with star-compatible coefficient order, an adjointable
`T : E → F` extends to the module completions. The forward continuous linear map is the
completion of `T`, and its adjoint is the completion of `T*`.

For the completion inclusions `j_E,j_F`, the formulas are `T̂ (j_E x) = j_F (T x)` and `T̂* (j_F
y) = j_E (T* y)`. The completed operator satisfies `‖T̂ x‖ ≤ ‖T‖ * ‖x‖` and `‖T̂‖ ≤ ‖T‖`.
Completeness of `E` and `F` is not required.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModule.AdjointableOperator

universe uB uE uF

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

attribute [local instance] CStarModule.completionCStarModule

/-- **Completion of an adjointable module map.** Let `B` be a nonunital complex C-star algebra
with star-compatible order on `Bᵐᵒᵖ`, and `E,F` complex normed right pre-Hilbert `B`-modules.
For `T : AdjointableOperator B E F`, complete its forward map and adjoint to obtain `T̂ :
Completion E → Completion F`, with `T̂(j_E x) = j_F(T x)` and `T̂*(j_F y) = j_E(T* y)`.
Neither fiber is required to be complete. -/
@[expose]
def completion (T : AdjointableOperator B E F) :
    AdjointableOperator B (UniformSpace.Completion E) (UniformSpace.Completion F) := by
  let f : UniformSpace.Completion E →L[ℂ] UniformSpace.Completion F :=
    ContinuousLinearMap.completion T.toContinuousLinearMap
  let g : UniformSpace.Completion F →L[ℂ] UniformSpace.Completion E :=
    ContinuousLinearMap.completion T.adjoint
  have hPair : ∀ (x : UniformSpace.Completion E) (y : UniformSpace.Completion F),
      CStarModule.rightInner (B := B) (f x) y =
        CStarModule.rightInner (B := B) x (g y) := by
    intro x y
    have hl : Continuous fun p : UniformSpace.Completion E × UniformSpace.Completion F =>
        CStarModule.rightInner (B := B) (f p.1) p.2 :=
      CStarModule.continuous_rightInner.comp
        ((f.continuous.comp continuous_fst).prodMk continuous_snd)
    have hr : Continuous fun p : UniformSpace.Completion E × UniformSpace.Completion F =>
        CStarModule.rightInner (B := B) p.1 (g p.2) :=
      CStarModule.continuous_rightInner.comp
        (continuous_fst.prodMk (g.continuous.comp continuous_snd))
    refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq hl hr) ?_
    intro a b
    dsimp only [f, g]
    rw [ContinuousLinearMap.completion_apply_coe,
      ContinuousLinearMap.completion_apply_coe]
    change MulOpposite.unop
        (inner Bᵐᵒᵖ ((T a : F) : UniformSpace.Completion F)
          (b : UniformSpace.Completion F)) =
      MulOpposite.unop
        (inner Bᵐᵒᵖ (a : UniformSpace.Completion E)
          ((T.adjoint b : E) : UniformSpace.Completion E))
    rw [CStarModule.completionCStarModule_inner_coe_coe,
      CStarModule.completionCStarModule_inner_coe_coe]
    exact T.adjoint_inner a b
  exact ofAdjointPair f g hPair

/-- **Forward map of the completed operator.** `(completion T).toContinuousLinearMap =
ContinuousLinearMap.completion T.toContinuousLinearMap`. -/
theorem completion_toContinuousLinearMap (T : AdjointableOperator B E F) :
    (completion T).toContinuousLinearMap =
      ContinuousLinearMap.completion T.toContinuousLinearMap :=
  rfl

/-- **Adjoint map of the completed operator.** `(completion T).adjoint =
ContinuousLinearMap.completion T.adjoint`. -/
theorem completion_adjoint (T : AdjointableOperator B E F) :
    (completion T).adjoint = ContinuousLinearMap.completion T.adjoint :=
  rfl

/-- **Completed operator on the dense inclusion.** `completion T (x : Completion E) = (T x :
Completion F)` for `x : E`. -/
@[simp]
theorem completion_apply_coe (T : AdjointableOperator B E F) (x : E) :
    completion T (x : UniformSpace.Completion E) =
      (T x : UniformSpace.Completion F) := by
  change (completion T).toContinuousLinearMap (x : UniformSpace.Completion E) = _
  rw [completion_toContinuousLinearMap]
  exact ContinuousLinearMap.completion_apply_coe T.toContinuousLinearMap x

/-- **Completed adjoint on the dense inclusion.** `(completion T).adjoint (y : Completion F) =
(T.adjoint y : Completion E)` for `y : F`. -/
@[simp]
theorem completion_adjoint_apply_coe (T : AdjointableOperator B E F) (y : F) :
    (completion T).adjoint (y : UniformSpace.Completion F) =
      (T.adjoint y : UniformSpace.Completion E) := by
  rw [completion_adjoint]
  exact ContinuousLinearMap.completion_apply_coe T.adjoint y

/-- **Completion commutes with adjoint operators.** `(completion T).adjointOperator = completion
T.adjointOperator`. -/
@[simp]
theorem completion_adjointOperator (T : AdjointableOperator B E F) :
    (completion T).adjointOperator = completion T.adjointOperator := by
  apply AdjointableOperator.ext
  intro y
  change (completion T).adjoint y =
    (completion T.adjointOperator).toContinuousLinearMap y
  rw [completion_adjoint, completion_toContinuousLinearMap]
  rfl

/-- **Vector norm bound after completion.** For `x : Completion E`, `‖completion T x‖ ≤ ‖T‖ *
‖x‖`. -/
theorem completion_norm_apply_le (T : AdjointableOperator B E F)
    (x : UniformSpace.Completion E) :
    ‖completion T x‖ ≤ ‖T‖ * ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (completion T).toContinuousLinearMap.continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro a
  rw [completion_apply_coe, UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe]
  calc
    ‖T a‖ = ‖T.toContinuousLinearMap a‖ := rfl
    _ ≤ ‖T.toContinuousLinearMap‖ * ‖a‖ := T.toContinuousLinearMap.le_opNorm a
    _ = ‖T‖ * ‖a‖ := by rw [AdjointableOperator.norm_eq]

/-- **Operator norm bound after completion.**
`‖completion T‖ ≤ ‖T‖` for the two completion norms. -/
theorem completion_norm_le (T : AdjointableOperator B E F) :
    ‖completion T‖ ≤ ‖T‖ := by
  rw [AdjointableOperator.norm_eq]
  exact ContinuousLinearMap.opNorm_le_bound _ (_root_.norm_nonneg T)
    (completion_norm_apply_le T)

end CStarModule.AdjointableOperator
