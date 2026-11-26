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

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.OfPair
public import MathlibExt.Analysis.CStarAlgebra.Module.Right
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Inner-product covectors on right C-star modules

Let `B` be a nonunital C-star algebra with a star-compatible order on `Bᵐᵒᵖ`, and let `E` be a
right C-star module. For `x : E`, the complex-linear covector `t_x : E →L[ℂ] B` is `t_x(y) =
rightInner x y`.

This map is adjointable, with adjoint `B →L[ℂ] E` given by `a ↦ x <• a`. The pairing identity is
`⟨t_x y, a⟩_B = ⟨y, x <• a⟩_B`. The definitions apply to pre-Hilbert modules and nonunital
coefficient algebras.
-/

@[expose] public section
noncomputable section
open scoped RightActions CStarModule.Right
namespace CStarModule.AdjointableOperator
universe uB uE
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/-- **Inner-product covector.** Let `E` be a right C-star module over a nonunital `B` with a
star-compatible order on `Bᵐᵒᵖ`. The complex-linear map `covectorCLM x : E →L[ℂ] B` sends `y`
to `rightInner x y`. -/
def covectorCLM (x : E) : E →L[ℂ] B :=
  (MulOpposite.opContinuousLinearEquiv ℂ (M := B)).symm.toContinuousLinearMap.comp
    (CStarModule.innerSL (A := Bᵐᵒᵖ) x)

theorem covectorCLM_apply (x y : E) :
    covectorCLM (B := B) x y = CStarModule.rightInner (B := B) x y := by
  rfl

/-- **Adjointable inner-product covector.** Let `E` be a right C-star module over a nonunital `B`
with a star-compatible order on `Bᵐᵒᵖ`. For `x : E`, the map `y ↦ rightInner x y` is
adjointable from `E` to `B`, with adjoint `a ↦ x <• a`. -/
def covector (x : E) : AdjointableOperator B E B :=
  ofAdjointPair (covectorCLM (B := B) x) (CStarModule.rightSMulCLM (B := B) x) <| by
    intro y a
    rw [covectorCLM_apply, CStarModule.Right.rightInner_self, CStarModule.rightSMulCLM_apply,
      CStarModule.rightInner_right_smul, CStarModule.star_rightInner]

theorem covector_toContinuousLinearMap (x : E) :
    (covector (B := B) x).toContinuousLinearMap = covectorCLM (B := B) x := by
  rfl

theorem covector_apply (x y : E) :
    covector (B := B) x y = CStarModule.rightInner (B := B) x y := by
  rfl

theorem covector_adjoint (x : E) :
    (covector (B := B) x).adjoint = CStarModule.rightSMulCLM (B := B) x := by
  rfl

theorem covector_adjoint_apply (x : E) (a : B) :
    (covector (B := B) x).adjoint a = x <• a := by
  rfl

end CStarModule.AdjointableOperator
