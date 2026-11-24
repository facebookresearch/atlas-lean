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
# Completion of rectangular adjointable module maps

The forward map and its given adjoint use the stock
`ContinuousLinearMap.completion` directly. The coefficient-valued adjoint
identity extends from the dense canonical images. The output uses exactly the
existing completion C-star-module factories and stock norms.

Neither component module is required to be complete. No nontriviality,
countability, new carrier, transported norm or global dictionary is assumed.
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

/-- Extend the given rectangular operator and its given adjoint to the
actual stock completions, with the existing coefficient-inner dictionaries. -/
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

/-- The completed forward map is definitionally the stock completion of the
same CLM. -/
theorem completion_toContinuousLinearMap (T : AdjointableOperator B E F) :
    (completion T).toContinuousLinearMap =
      ContinuousLinearMap.completion T.toContinuousLinearMap :=
  rfl

/-- The stored completed adjoint is definitionally the stock completion of
the given adjoint CLM. -/
theorem completion_adjoint (T : AdjointableOperator B E F) :
    (completion T).adjoint = ContinuousLinearMap.completion T.adjoint :=
  rfl

/-- The canonical completion image keeps the original forward value. -/
@[simp]
theorem completion_apply_coe (T : AdjointableOperator B E F) (x : E) :
    completion T (x : UniformSpace.Completion E) =
      (T x : UniformSpace.Completion F) := by
  change (completion T).toContinuousLinearMap (x : UniformSpace.Completion E) = _
  rw [completion_toContinuousLinearMap]
  exact ContinuousLinearMap.completion_apply_coe T.toContinuousLinearMap x

/-- The canonical completion image keeps the original adjoint value. -/
@[simp]
theorem completion_adjoint_apply_coe (T : AdjointableOperator B E F) (y : F) :
    (completion T).adjoint (y : UniformSpace.Completion F) =
      (T.adjoint y : UniformSpace.Completion E) := by
  rw [completion_adjoint]
  exact ContinuousLinearMap.completion_apply_coe T.adjoint y

/-- Completion retains the actual adjoint operator in both directions. -/
@[simp]
theorem completion_adjointOperator (T : AdjointableOperator B E F) :
    (completion T).adjointOperator = completion T.adjointOperator := by
  apply AdjointableOperator.ext
  intro y
  change (completion T).adjoint y =
    (completion T.adjointOperator).toContinuousLinearMap y
  rw [completion_adjoint, completion_toContinuousLinearMap]
  rfl

/-- The completed map has the original operator-norm bound at every vector. -/
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

/-- The completed operator needs no larger norm bound than the given operator. -/
theorem completion_norm_le (T : AdjointableOperator B E F) :
    ‖completion T‖ ≤ ‖T‖ := by
  rw [AdjointableOperator.norm_eq]
  exact ContinuousLinearMap.opNorm_le_bound _ (_root_.norm_nonneg T)
    (completion_norm_apply_le T)

end CStarModule.AdjointableOperator
