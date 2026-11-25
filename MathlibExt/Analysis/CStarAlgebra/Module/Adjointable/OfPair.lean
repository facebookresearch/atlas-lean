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

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Constructing adjointable operators from an adjoint pair

This file packages the source-oriented right-inner-product equation into the
existing `AdjointableOperator` structure.  It introduces no new operator
carrier or typeclass instance.
-/

@[expose] public section

namespace CStarModule.AdjointableOperator

universe uB uE uF

variable {B : Type uB} {E : Type uE} {F : Type uF}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F]

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E and F be
normed right inner-product modules over B, with compatible complex normed-space structures.

If bounded complex-linear maps T : E → F and S : F → E satisfy ⟨Tx, y⟩ = ⟨x, Sy⟩ for every x ∈ E
and y ∈ F, they define an adjointable operator with forward map T and adjoint S.
-/
def ofAdjointPair
    (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y,
      CStarModule.rightInner (B := B) (T x) y =
        CStarModule.rightInner (B := B) x (S y)) :
    AdjointableOperator B E F where
  toContinuousLinearMap := T
  adjoint := S
  isAdjointPair' := (isAdjointPair_iff_adjoint_inner T S).2 h

@[simp]
theorem ofAdjointPair_toContinuousLinearMap
    (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y,
      CStarModule.rightInner (B := B) (T x) y =
        CStarModule.rightInner (B := B) x (S y)) :
    (ofAdjointPair T S h).toContinuousLinearMap = T :=
  rfl

@[simp]
theorem ofAdjointPair_adjoint
    (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y,
      CStarModule.rightInner (B := B) (T x) y =
        CStarModule.rightInner (B := B) x (S y)) :
    (ofAdjointPair T S h).adjoint = S :=
  rfl

@[simp]
theorem ofAdjointPair_apply
    (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (h : ∀ x y,
      CStarModule.rightInner (B := B) (T x) y =
        CStarModule.rightInner (B := B) x (S y))
    (x : E) :
    ofAdjointPair T S h x = T x :=
  rfl

end CStarModule.AdjointableOperator
