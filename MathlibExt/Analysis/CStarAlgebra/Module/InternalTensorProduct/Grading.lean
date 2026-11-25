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

public import MathlibExt.Analysis.CStarAlgebra.Grading.Module.Transport
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Semilinear
public import
  MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.ModelComparison.Completion

/-!
# Gradings on completed internal tensors

The factor grading generators specialize the coefficient-changing equivalence
of the actual balanced tensor, radical quotient and completion. Its original
inner covariance and isometry provide the generator on that same completed
module. Two evaluations on the dense pure span prove involutivity.

The constructed unitary comparison transports this grading to any existing
genuine completed internal-tensor model, with the same metric and coefficient
action. The pure-generator characteristic is unsigned in both cases.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped RightActions

namespace CStarModule.InternalTensorProduct.Grading

universe uB₁ uB₂ uE₁ uE₂ uX

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]
variable {γ₁ : CStarGrading B₁} {γ₂ : CStarGrading B₂}

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂. Suppose B₁ and B₂ have
involutive C*-algebra gradings γ₁ and γ₂, the modules have compatible gradings δ₁ and δ₂, and φ
is equivariant from γ₁ to the induced operator grading on E₂.

The completed internal tensor carries a compatible module grading whose generator acts on pure
vectors by pure(x,y) ↦ pure(δ₁(x),δ₂(y)).
-/
def completedGrading
    (δ₁ : CStarModuleGrading γ₁ E₁) (δ₂ : CStarModuleGrading γ₂ E₂)
    (φ : CStarGrading.Hom γ₁ δ₂.operatorGrading) :
    letI : NormedAddCommGroup
        (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
      radicalTensorNormedAddCommGroup φ.toNonUnitalStarAlgHom;
    letI : NormedSpace ℂ
        (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
      radicalTensorNormedSpace φ.toNonUnitalStarAlgHom;
    letI : SMul B₂ᵐᵒᵖ
        (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
      radicalRightAction φ.toNonUnitalStarAlgHom;
    letI : CStarModule B₂ᵐᵒᵖ
        (CompletedTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
      completedCStarModule φ.toNonUnitalStarAlgHom;
    CStarModuleGrading γ₂
      (CompletedTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) := by
  let ψ := φ.toNonUnitalStarAlgHom
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) ψ) :=
    radicalTensorNormedAddCommGroup ψ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) ψ) :=
    radicalTensorNormedSpace ψ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) ψ) := radicalRightAction ψ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) ψ) :=
    completedCStarModule ψ
  have hφ : ∀ (b : B₁) (y : E₂),
      δ₂.generator (ψ b y) = ψ (γ₁.generatorAut b) (δ₂.generator y) := by
    intro b y
    have he := CStarGrading.Hom.equivariant φ 1 b
    change ψ (γ₁.generatorAut b) = δ₂.operatorGrading.generatorAut (ψ b) at he
    have hy := congrArg
      (fun T : CStarModule.AdjointableOperator.End B₂ E₂ =>
        T (δ₂.generator y)) he
    rw [CStarModuleGrading.operatorGrading_generatorAut,
      CStarModuleGrading.operatorGenerator_apply, δ₂.generator_involutive] at hy
    exact hy.symm
  let T := CompletedTensor (E₁ := E₁) ψ
  let U : T ≃ₗᵢ[ℂ] T := completedSemilinearEquiv
    ψ ψ γ₁.generatorAut γ₂.generatorAut
    δ₁.generator.toLinearEquiv δ₂.generator.toLinearEquiv
    δ₁.generator_rightInner δ₂.generator_rightInner hφ
  have hUPure (x : E₁) (y : E₂) :
      U (completedPure ψ x y) =
        completedPure ψ (δ₁.generator x) (δ₂.generator y) := by
    exact completedSemilinearEquiv_pure
      ψ ψ γ₁.generatorAut γ₂.generatorAut
      δ₁.generator.toLinearEquiv δ₂.generator.toLinearEquiv
      δ₁.generator_rightInner δ₂.generator_rightInner hφ x y
  have hUSquare :
      U.toLinearIsometry.toContinuousLinearMap.comp
          U.toLinearIsometry.toContinuousLinearMap =
        ContinuousLinearMap.id ℂ T := by
    apply ContinuousLinearMap.ext_on (completedPure_dense_span ψ)
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change U (U (completedPure ψ x y)) = completedPure ψ x y
    rw [hUPure, hUPure, δ₁.generator_involutive, δ₂.generator_involutive]
  have hUInvolutive : Function.Involutive U := by
    intro z
    have hz := congrArg (fun L : T →L[ℂ] T => L z) hUSquare
    change U (U z) = z at hz
    exact hz
  exact
    { generator := U.toContinuousLinearEquiv
      generator_involutive := hUInvolutive
      generator_right_smul := completedSemilinearEquiv_right_smul
        ψ ψ γ₁.generatorAut γ₂.generatorAut
        δ₁.generator.toLinearEquiv δ₂.generator.toLinearEquiv
        δ₁.generator_rightInner δ₂.generator_rightInner hφ
      generator_rightInner := completedSemilinearEquiv_rightInner
        ψ ψ γ₁.generatorAut γ₂.generatorAut
        δ₁.generator.toLinearEquiv δ₂.generator.toLinearEquiv
        δ₁.generator_rightInner δ₂.generator_rightInner hφ }

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂. Suppose B₁ and B₂ have
involutive C*-algebra gradings γ₁ and γ₂, the modules have compatible gradings δ₁ and δ₂, and φ
is equivariant from γ₁ to the induced operator grading on E₂.

The generator of the completed grading sends completedPure(x,y) to completedPure(δ₁(x),δ₂(y)).
-/
@[simp]
theorem completedGrading_generator_pure
    (δ₁ : CStarModuleGrading γ₁ E₁) (δ₂ : CStarModuleGrading γ₂ E₂)
    (φ : CStarGrading.Hom γ₁ δ₂.operatorGrading) (x : E₁) (y : E₂) :
    letI : NormedAddCommGroup
        (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
      radicalTensorNormedAddCommGroup φ.toNonUnitalStarAlgHom;
    letI : NormedSpace ℂ
        (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
      radicalTensorNormedSpace φ.toNonUnitalStarAlgHom;
    letI : SMul B₂ᵐᵒᵖ
        (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
      radicalRightAction φ.toNonUnitalStarAlgHom;
    letI : CStarModule B₂ᵐᵒᵖ
        (CompletedTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
      completedCStarModule φ.toNonUnitalStarAlgHom;
    (completedGrading δ₁ δ₂ φ).generator
        (completedPure φ.toNonUnitalStarAlgHom x y) =
      completedPure φ.toNonUnitalStarAlgHom
        (δ₁.generator x) (δ₂.generator y) := by
  let ψ := φ.toNonUnitalStarAlgHom
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) ψ) :=
    radicalTensorNormedAddCommGroup ψ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) ψ) :=
    radicalTensorNormedSpace ψ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) ψ) := radicalRightAction ψ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) ψ) :=
    completedCStarModule ψ
  have hφ : ∀ (b : B₁) (y : E₂),
      δ₂.generator (ψ b y) = ψ (γ₁.generatorAut b) (δ₂.generator y) := by
    intro b y
    have he := CStarGrading.Hom.equivariant φ 1 b
    change ψ (γ₁.generatorAut b) = δ₂.operatorGrading.generatorAut (ψ b) at he
    have hy := congrArg
      (fun T : CStarModule.AdjointableOperator.End B₂ E₂ =>
        T (δ₂.generator y)) he
    rw [CStarModuleGrading.operatorGrading_generatorAut,
      CStarModuleGrading.operatorGenerator_apply, δ₂.generator_involutive] at hy
    exact hy.symm
  change completedSemilinearEquiv
      ψ ψ γ₁.generatorAut γ₂.generatorAut
      δ₁.generator.toLinearEquiv δ₂.generator.toLinearEquiv
      δ₁.generator_rightInner δ₂.generator_rightInner hφ
        (completedPure ψ x y) = _
  exact completedSemilinearEquiv_pure
    ψ ψ γ₁.generatorAut γ₂.generatorAut
    δ₁.generator.toLinearEquiv δ₂.generator.toLinearEquiv
    δ₁.generator_rightInner δ₂.generator_rightInner hφ x y

section Model

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [SMul B₂ᵐᵒᵖ X] [CStarModule B₂ᵐᵒᵖ X] [CompleteSpace X]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂. Suppose B₁ and B₂ have
involutive C*-algebra gradings γ₁ and γ₂, the modules have compatible gradings δ₁ and δ₂, and φ
is equivariant from γ₁ to the induced operator grading on E₂. Let X be a complete normed right
inner-product B₂-module with a compatible complex normed-space structure, and let pure : E₁ × E₂
→ X satisfy the internal-tensor laws with dense pure span in X.

The module X carries a compatible grading whose generator sends pure(x,y) to pure(δ₁(x),δ₂(y)).
-/
def modelGrading
    (δ₁ : CStarModuleGrading γ₁ E₁) (δ₂ : CStarModuleGrading γ₂ E₂)
    (φ : CStarGrading.Hom γ₁ δ₂.operatorGrading) (pure : E₁ → E₂ → X)
    (hX : IsModel φ.toNonUnitalStarAlgHom pure) :
    CStarModuleGrading γ₂ X := by
  letI : NormedAddCommGroup
      (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
    radicalTensorNormedAddCommGroup φ.toNonUnitalStarAlgHom
  letI : NormedSpace ℂ
      (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
    radicalTensorNormedSpace φ.toNonUnitalStarAlgHom
  letI : SMul B₂ᵐᵒᵖ
      (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
    radicalRightAction φ.toNonUnitalStarAlgHom
  letI : CStarModule B₂ᵐᵒᵖ
      (CompletedTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
    completedCStarModule φ.toNonUnitalStarAlgHom
  exact CStarModuleGrading.transport (completedGrading δ₁ δ₂ φ)
    (completedTensorModelUnitary φ.toNonUnitalStarAlgHom pure hX)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with star-compatible partial orders on
their opposite algebras. Let E₁ and E₂ be complete normed right inner-product modules over B₁
and B₂, respectively, with compatible complex normed-space structures. Let φ be a nonunital
complex star representation of B₁ by adjointable endomorphisms of E₂. Suppose B₁ and B₂ have
involutive C*-algebra gradings γ₁ and γ₂, the modules have compatible gradings δ₁ and δ₂, and φ
is equivariant from γ₁ to the induced operator grading on E₂. Let X be a complete normed right
inner-product B₂-module with a compatible complex normed-space structure, and let pure : E₁ × E₂
→ X satisfy the internal-tensor laws with dense pure span in X.

The generator of the grading on X sends pure(x,y) to pure(δ₁(x),δ₂(y)).
-/
@[simp]
theorem modelGrading_generator_pure
    (δ₁ : CStarModuleGrading γ₁ E₁) (δ₂ : CStarModuleGrading γ₂ E₂)
    (φ : CStarGrading.Hom γ₁ δ₂.operatorGrading) (pure : E₁ → E₂ → X)
    (hX : IsModel φ.toNonUnitalStarAlgHom pure) (x : E₁) (y : E₂) :
    (modelGrading δ₁ δ₂ φ pure hX).generator (pure x y) =
      pure (δ₁.generator x) (δ₂.generator y) := by
  let : NormedAddCommGroup
      (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
    radicalTensorNormedAddCommGroup φ.toNonUnitalStarAlgHom
  let : NormedSpace ℂ
      (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
    radicalTensorNormedSpace φ.toNonUnitalStarAlgHom
  let : SMul B₂ᵐᵒᵖ
      (RadicalTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
    radicalRightAction φ.toNonUnitalStarAlgHom
  let : CStarModule B₂ᵐᵒᵖ
      (CompletedTensor (E₁ := E₁) φ.toNonUnitalStarAlgHom) :=
    completedCStarModule φ.toNonUnitalStarAlgHom
  change (CStarModuleGrading.transport (completedGrading δ₁ δ₂ φ)
      (completedTensorModelUnitary φ.toNonUnitalStarAlgHom pure hX)).generator
      (pure x y) = _
  rw [CStarModuleGrading.transport_generator_apply,
    completedTensorModelUnitary_symm_pure, completedGrading_generator_pure,
    completedTensorModelUnitary_pure]

end Model

end CStarModule.InternalTensorProduct.Grading
