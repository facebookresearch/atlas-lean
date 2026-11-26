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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Iterated
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Grading
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.GradedLeft

/-!
# Graded coefficient actions on an internal tensor

Let graded nonunital C-star algebras `D₁,D₂,B` with star-compatible opposite orders act on
complete graded right modules `E₂,E₃`, through graded star homomorphisms `φ : D₁ → End_(D₂)(E₂)`
and `χ : D₂ → End_B(E₃)`. The tensor grading on `E₂ ⊗_χ E₃` is generated on pure vectors by
`Γ(y⊗z) = δ₂(y)⊗δ₃(z)`.

The induced coefficient action `η(b)(y⊗z) = φ(b)y⊗z` is graded: `Γ η(b) = η(γ_(D₁)(b)) Γ`. Its
underlying nonunital star homomorphism is the induced completed left action, with the same
pure-vector values.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped RightActions

namespace CStarModule.InternalTensorProduct

universe uD1 uD2 uB uE2 uE3

variable {D1 : Type uD1} [NonUnitalCStarAlgebra D1]
  [PartialOrder D1ᵐᵒᵖ] [StarOrderedRing D1ᵐᵒᵖ]
variable {D2 : Type uD2} [NonUnitalCStarAlgebra D2]
  [PartialOrder D2ᵐᵒᵖ] [StarOrderedRing D2ᵐᵒᵖ]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E2 : Type uE2} [NormedAddCommGroup E2] [NormedSpace ℂ E2]
  [SMul D2ᵐᵒᵖ E2] [CStarModule D2ᵐᵒᵖ E2] [CompleteSpace E2]
variable {E3 : Type uE3} [NormedAddCommGroup E3] [NormedSpace ℂ E3]
  [SMul Bᵐᵒᵖ E3] [CStarModule Bᵐᵒᵖ E3] [CompleteSpace E3]
variable {gammaD1 : CStarGrading D1} {gammaD2 : CStarGrading D2} {gammaB : CStarGrading B}

/-- **Graded coefficient representation on the inner tensor.** Let `D₁,D₂,B` be graded nonunital
C-star algebras with star-compatible opposite orders, and `E₂,E₃` complete graded right
modules over `D₂,B`. For graded complex nonunital star homomorphisms `φ : D₁ → End_(D₂)(E₂)`
and `χ : D₂ → End_B(E₃)`, the induced action on `E₂ ⊗_χ E₃` satisfies `η(b)(y⊗z) = φ(b)y⊗z`
and intertwines the tensor grading with that of `D₁`. -/
def inducedCompletedGradedLeftAction
    (delta2 : CStarModuleGrading gammaD2 E2) (delta3 : CStarModuleGrading gammaB E3)
    (phi : CStarGrading.Hom gammaD1 delta2.operatorGrading)
    (chi : CStarGrading.Hom gammaD2 delta3.operatorGrading) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalTensorNormedAddCommGroup chi.toNonUnitalStarAlgHom
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalTensorNormedSpace chi.toNonUnitalStarAlgHom
    letI : SMul Bᵐᵒᵖ (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalRightAction chi.toNonUnitalStarAlgHom
    letI : CStarModule Bᵐᵒᵖ (CompletedTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      completedCStarModule chi.toNonUnitalStarAlgHom
    CStarGrading.Hom gammaD1 (Grading.completedGrading delta2 delta3 chi).operatorGrading := by
  let psi := chi.toNonUnitalStarAlgHom
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E2) psi) := radicalTensorNormedAddCommGroup psi
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E2) psi) := radicalTensorNormedSpace psi
  letI : SMul Bᵐᵒᵖ (RadicalTensor (E₁ := E2) psi) := radicalRightAction psi
  letI : CStarModule Bᵐᵒᵖ (CompletedTensor (E₁ := E2) psi) := completedCStarModule psi
  let delta23 := Grading.completedGrading delta2 delta3 chi
  let gradedAction := CStarGrading.Hom.comp
    (IsModel.gradedLeftHom (completed_isModel (E₁ := E2) psi)
      delta2 delta3 delta23
      (Grading.completedGrading_generator_pure delta2 delta3 chi)) phi
  have hAction : gradedAction.toNonUnitalStarAlgHom =
      inducedCompletedLeftAction phi.toNonUnitalStarAlgHom psi := by
    change (IsModel.mapLeftStarAlgHom (completed_isModel (E₁ := E2) psi)).toNonUnitalStarAlgHom.comp
        phi.toNonUnitalStarAlgHom =
      (completedLeftStarAlgHom (E₁ := E2) psi).toNonUnitalStarAlgHom.comp phi.toNonUnitalStarAlgHom
    rw [CStarModule.InternalTensorProduct.mapLeftStarAlgHom_completed]
  refine
    { toNonUnitalStarAlgHom := inducedCompletedLeftAction phi.toNonUnitalStarAlgHom psi
      equivariant' := ?_ }
  intro n b
  change inducedCompletedLeftAction phi.toNonUnitalStarAlgHom psi
      (PointNormCStarAddAction.aut gammaD1 n.toAdd b) =
    PointNormCStarAddAction.aut delta23.operatorGrading n.toAdd
      (inducedCompletedLeftAction phi.toNonUnitalStarAlgHom psi b)
  have h := gradedAction.equivariant' n b
  change gradedAction.toNonUnitalStarAlgHom
      (PointNormCStarAddAction.aut gammaD1 n.toAdd b) =
    PointNormCStarAddAction.aut delta23.operatorGrading n.toAdd
      (gradedAction.toNonUnitalStarAlgHom b) at h
  simpa only [hAction] using h

omit [PartialOrder D1ᵐᵒᵖ] [StarOrderedRing D1ᵐᵒᵖ] in
/-- **Underlying star homomorphism of the graded action.** For the same graded actions `φ,χ`, the
underlying homomorphism of `inducedCompletedGradedLeftAction` equals
`inducedCompletedLeftAction φ.toNonUnitalStarAlgHom χ.toNonUnitalStarAlgHom`. -/
@[simp]
theorem inducedCompletedGradedLeftAction_toNonUnitalStarAlgHom
    (delta2 : CStarModuleGrading gammaD2 E2) (delta3 : CStarModuleGrading gammaB E3)
    (phi : CStarGrading.Hom gammaD1 delta2.operatorGrading)
    (chi : CStarGrading.Hom gammaD2 delta3.operatorGrading) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalTensorNormedAddCommGroup chi.toNonUnitalStarAlgHom
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalTensorNormedSpace chi.toNonUnitalStarAlgHom
    letI : SMul Bᵐᵒᵖ (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalRightAction chi.toNonUnitalStarAlgHom
    letI : CStarModule Bᵐᵒᵖ (CompletedTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      completedCStarModule chi.toNonUnitalStarAlgHom
    (inducedCompletedGradedLeftAction delta2 delta3 phi chi).toNonUnitalStarAlgHom =
      inducedCompletedLeftAction phi.toNonUnitalStarAlgHom chi.toNonUnitalStarAlgHom := rfl

omit [PartialOrder D1ᵐᵒᵖ] [StarOrderedRing D1ᵐᵒᵖ] in
/-- **Graded coefficient action on pure tensors.** The induced graded map sends `completedPure χ y
z` to `completedPure χ (φ b y) z` for each coefficient `b : D₁`. -/
@[simp]
theorem inducedCompletedGradedLeftAction_pure
    (delta2 : CStarModuleGrading gammaD2 E2) (delta3 : CStarModuleGrading gammaB E3)
    (phi : CStarGrading.Hom gammaD1 delta2.operatorGrading)
    (chi : CStarGrading.Hom gammaD2 delta3.operatorGrading) (b : D1) (y : E2) (z : E3) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalTensorNormedAddCommGroup chi.toNonUnitalStarAlgHom
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalTensorNormedSpace chi.toNonUnitalStarAlgHom
    letI : SMul Bᵐᵒᵖ (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalRightAction chi.toNonUnitalStarAlgHom
    letI : CStarModule Bᵐᵒᵖ (CompletedTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      completedCStarModule chi.toNonUnitalStarAlgHom
    inducedCompletedGradedLeftAction delta2 delta3 phi chi b (completedPure chi.toNonUnitalStarAlgHom y z) =
      completedPure chi.toNonUnitalStarAlgHom (phi b y) z :=
  by
    let : NormedAddCommGroup (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalTensorNormedAddCommGroup chi.toNonUnitalStarAlgHom
    let : NormedSpace ℂ (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalTensorNormedSpace chi.toNonUnitalStarAlgHom
    let : SMul Bᵐᵒᵖ (RadicalTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      radicalRightAction chi.toNonUnitalStarAlgHom
    let : CStarModule Bᵐᵒᵖ (CompletedTensor (E₁ := E2) chi.toNonUnitalStarAlgHom) :=
      completedCStarModule chi.toNonUnitalStarAlgHom
    have hview (a : D1) : phi.toNonUnitalStarAlgHom a = phi a := rfl
    have hwrapped (a : D1) : inducedCompletedGradedLeftAction delta2 delta3 phi chi a =
        (inducedCompletedGradedLeftAction delta2 delta3 phi chi).toNonUnitalStarAlgHom a := rfl
    rw [hwrapped, inducedCompletedGradedLeftAction_toNonUnitalStarAlgHom]
    simpa only [hview] using
      inducedCompletedLeftAction_completedPure phi.toNonUnitalStarAlgHom chi.toNonUnitalStarAlgHom b y z

end CStarModule.InternalTensorProduct
