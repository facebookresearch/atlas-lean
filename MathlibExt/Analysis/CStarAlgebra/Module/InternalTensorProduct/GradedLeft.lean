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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Grading
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.ModelComparison.Left
import Mathlib.Tactic.FinCases

/-!
# The actual graded left internal-tensor homomorphism

This bundles the computed ordinary left End homomorphism with its grading
covariance. The proof evaluates it on the model's dense pure span. It does not
supply or choose a left operator, grading, norm, model or equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarModule.InternalTensorProduct.IsModel

universe uD uB uE1 uE2 uX

variable {D : Type uD} [NonUnitalCStarAlgebra D]
  [PartialOrder Dᵐᵒᵖ] [StarOrderedRing Dᵐᵒᵖ]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E1 : Type uE1} [NormedAddCommGroup E1] [NormedSpace ℂ E1]
  [SMul Dᵐᵒᵖ E1] [CStarModule Dᵐᵒᵖ E1] [CompleteSpace E1]
variable {E2 : Type uE2} [NormedAddCommGroup E2] [NormedSpace ℂ E2]
  [SMul Bᵐᵒᵖ E2] [CStarModule Bᵐᵒᵖ E2] [CompleteSpace E2]
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [SMul Bᵐᵒᵖ X] [CStarModule Bᵐᵒᵖ X] [CompleteSpace X]
variable {γD : CStarGrading D} {γB : CStarGrading B}
variable {φ : D →⋆ₙₐ[ℂ] CStarModule.AdjointableOperator.End B E2}
variable {pure : E1 → E2 → X}

/--
Let D and B be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras and involutive C*-algebra gradings γD and γB. Let E₁ be a complete
normed right inner-product D-module and let E₂ and X be complete normed right inner-product
B-modules, all with compatible complex normed-space structures. Let φ be a nonunital complex
star representation of D by adjointable endomorphisms of E₂, and let pure : E₁ × E₂ → X satisfy
the internal-tensor laws with dense pure span in X.

If module gradings δ₁, δ₂ and δX are compatible with their coefficient gradings and satisfy
δX(pure(x,y)) = pure(δ₁(x),δ₂(y)), the tensor-extension homomorphism from the adjointable
endomorphisms of E₁ to those of X respects the induced operator gradings.
-/
def gradedLeftHom
    (hX : CStarModule.InternalTensorProduct.IsModel φ pure)
    (δ1 : CStarModuleGrading γD E1) (δ2 : CStarModuleGrading γB E2)
    (δX : CStarModuleGrading γB X)
    (hGrading : ∀ x y, δX.generator (pure x y) =
      pure (δ1.generator x) (δ2.generator y)) :
    CStarGrading.Hom δ1.operatorGrading δX.operatorGrading where
  toNonUnitalStarAlgHom := hX.mapLeftStarAlgHom.toNonUnitalStarAlgHom
  equivariant' := by
    intro n T
    change hX.mapLeftStarAlgHom (PointNormCStarAddAction.aut δ1.operatorGrading n.toAdd T) =
      PointNormCStarAddAction.aut δX.operatorGrading n.toAdd (hX.mapLeftStarAlgHom T)
    have hn (k : ZMod 2) : k = 0 ∨ k = 1 := by
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hn n.toAdd with h0 | h1
    · rw [h0]
      simp only [PointNormCStarAddAction.aut_zero, StarAlgEquiv.one_apply]
    · rw [h1]
      apply CStarModule.AdjointableOperator.toContinuousLinearMap_injective
      apply ContinuousLinearMap.ext_on hX.2.2.2.2.2.2.2
      rintro _ ⟨⟨x, y⟩, rfl⟩
      change hX.mapLeftStarAlgHom (δ1.operatorGrading.generatorAut T) (pure x y) =
        δX.operatorGrading.generatorAut (hX.mapLeftStarAlgHom T) (pure x y)
      rw [CStarModuleGrading.operatorGrading_generatorAut,
        CStarModuleGrading.operatorGrading_generatorAut,
        mapLeftStarAlgHom_pure, CStarModuleGrading.operatorGenerator_apply,
        CStarModuleGrading.operatorGenerator_apply, hGrading,
        mapLeftStarAlgHom_pure, hGrading, δ2.generator_involutive]

end CStarModule.InternalTensorProduct.IsModel
