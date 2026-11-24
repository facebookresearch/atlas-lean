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
# Original inner-product covectors on a right C-star module

The forward continuous map reuses the actual CStarModule.innerSL and the
canonical unop transport. Its adjoint is the existing rightSMulCLM x.
Only their defining right-inner pairing equation is proved to bundle the
adjointable covector. No compactness, exact norm, Riesz theorem or supplied
covector model constructs this DATA.
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

/-- The original B-valued inner-product functional at x. -/
def covectorCLM (x : E) : E →L[ℂ] B :=
  (MulOpposite.opContinuousLinearEquiv ℂ (M := B)).symm.toContinuousLinearMap.comp
    (CStarModule.innerSL (A := Bᵐᵒᵖ) x)

theorem covectorCLM_apply (x y : E) :
    covectorCLM (B := B) x y = CStarModule.rightInner (B := B) x y := by
  rfl

/-- The actual adjointable t_x, without a unit on B or any chosen source output. -/
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
