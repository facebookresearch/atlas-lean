/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapLeft.Completion

/-!
# The actual left star homomorphism on the completed internal tensor

The computed left tensor operators satisfy the unit, addition, composition,
complex scalar and star laws on pure tensors. The already proved dense
complex linear span and stock CLM extensionality prove equality of the
actual operators. The resulting star homomorphism is real data on the
literal completed tensor, not a supplied representation or model.

This is Blackadar13.5.1's F tensor1 construction. Faithful-phi injectivity,
norm equality, compact preservation, graded transport and comparison
with arbitrary supplied completed models are separate obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. The identity endomorphism of E₁ induces the identity endomorphism of the completed tensor
product. -/
@[simp]
theorem completedLeftOperator_one
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedLeftOperator φ (1 : AdjointableOperator.End B₁ E₁) = 1 := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  apply AdjointableOperator.toContinuousLinearMap_injective
  apply ContinuousLinearMap.ext_on (completedPure_dense_span φ)
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change completedLeftOperator φ (1 : AdjointableOperator.End B₁ E₁)
      (completedPure φ x y) =
    (1 : AdjointableOperator.End B₂ (CompletedTensor (E₁ := E₁) φ))
      (completedPure φ x y)
  rw [completedLeftOperator_pure, AdjointableOperator.one_apply,
    AdjointableOperator.one_apply]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. The induced first-factor operator of a sum is the sum of the induced operators. -/
theorem completedLeftOperator_add
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L M : AdjointableOperator.End B₁ E₁) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedLeftOperator φ (L + M) =
      completedLeftOperator φ L + completedLeftOperator φ M := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  apply AdjointableOperator.toContinuousLinearMap_injective
  apply ContinuousLinearMap.ext_on (completedPure_dense_span φ)
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change completedLeftOperator φ (L + M) (completedPure φ x y) =
    (completedLeftOperator φ L + completedLeftOperator φ M) (completedPure φ x y)
  rw [completedLeftOperator_pure, AdjointableOperator.add_apply,
    AdjointableOperator.add_apply, completedPure_add_left,
    completedLeftOperator_pure, completedLeftOperator_pure]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Composition of first-factor endomorphisms is carried to composition of their induced
operators. -/
theorem completedLeftOperator_mul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L M : AdjointableOperator.End B₁ E₁) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedLeftOperator φ (L * M) =
      completedLeftOperator φ L * completedLeftOperator φ M := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  apply AdjointableOperator.toContinuousLinearMap_injective
  apply ContinuousLinearMap.ext_on (completedPure_dense_span φ)
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change completedLeftOperator φ (L * M) (completedPure φ x y) =
    (completedLeftOperator φ L * completedLeftOperator φ M) (completedPure φ x y)
  rw [completedLeftOperator_pure, AdjointableOperator.mul_apply,
    AdjointableOperator.mul_apply, completedLeftOperator_pure,
    completedLeftOperator_pure]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Multiplying a first-factor operator by a complex scalar multiplies its induced operator by
the same scalar. -/
theorem completedLeftOperator_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (c : ℂ) (L : AdjointableOperator.End B₁ E₁) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedLeftOperator φ (c • L) = c • completedLeftOperator φ L := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  apply AdjointableOperator.toContinuousLinearMap_injective
  apply ContinuousLinearMap.ext_on (completedPure_dense_span φ)
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change completedLeftOperator φ (c • L) (completedPure φ x y) =
    (c • completedLeftOperator φ L) (completedPure φ x y)
  rw [completedLeftOperator_pure, AdjointableOperator.smul_apply,
    AdjointableOperator.smul_apply, completedPure_smul_left,
    completedLeftOperator_pure]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Taking the adjoint of a first-factor operator takes the adjoint of its induced operator. -/
theorem completedLeftOperator_star
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator.End B₁ E₁) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedLeftOperator φ (star L) = star (completedLeftOperator φ L) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  apply AdjointableOperator.toContinuousLinearMap_injective
  apply ContinuousLinearMap.ext_on (completedPure_dense_span φ)
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change completedLeftOperator φ (star L) (completedPure φ x y) =
    star (completedLeftOperator φ L) (completedPure φ x y)
  rw [completedLeftOperator_pure, AdjointableOperator.star_apply,
    AdjointableOperator.star_apply, completedLeftOperator_adjoint_pure]

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. First-factor endomorphisms define a unital complex star algebra homomorphism into the
adjointable endomorphisms of the completed tensor product. -/
def completedLeftStarAlgHom
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    AdjointableOperator.End B₁ E₁ →⋆ₐ[ℂ]
      AdjointableOperator.End B₂ (CompletedTensor (E₁ := E₁) φ) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  let f : AdjointableOperator.End B₁ E₁ →ₗ[ℂ]
      AdjointableOperator.End B₂ (CompletedTensor (E₁ := E₁) φ) :=
    { toFun := fun L => completedLeftOperator φ L
      map_add' := completedLeftOperator_add φ
      map_smul' := completedLeftOperator_smul φ }
  exact
    { toAlgHom := AlgHom.ofLinearMap f (completedLeftOperator_one φ)
        (completedLeftOperator_mul φ)
      map_star' := completedLeftOperator_star φ }

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. This star algebra homomorphism evaluates to the induced first-factor adjointable operator. -/
theorem completedLeftStarAlgHom_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator.End B₁ E₁) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedLeftStarAlgHom φ L = completedLeftOperator φ L := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  rfl

/-- Let B₁ and B₂ be possibly nonunital complex C-star algebras, E₁ and E₂ complete right Hilbert
modules over them, and φ a nonunital star representation of B₁ by B₂-adjointable operators on
E₂. Its value at L sends the pure tensor of x and y to the pure tensor of Lx and y. -/
@[simp]
theorem completedLeftStarAlgHom_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator.End B₁ E₁) (x : E₁) (y : E₂) :
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ;
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ;
  letI : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ;
  letI : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ;
    completedLeftStarAlgHom φ L (completedPure φ x y) = completedPure φ (L x) y := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedSpace φ
  let : SMul B₂ᵐᵒᵖ (RadicalTensor (E₁ := E₁) φ) := radicalRightAction φ
  let : CStarModule B₂ᵐᵒᵖ (CompletedTensor (E₁ := E₁) φ) := completedCStarModule φ
  rw [completedLeftStarAlgHom_apply, completedLeftOperator_pure]

end CStarModule.InternalTensorProduct
