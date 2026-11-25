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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Radical

/-!
# Left adjointable maps on algebraic internal tensors

An actual adjointable right-module map on the first factor induces a
complex-linear map on the ordinary, balanced and radical tensor carriers.
Its actual adjoint induces the paired map in the reverse direction.

These are algebraic quotient maps. No norm, completeness, completed
operator or supplied tensor-model witness is introduced. The source is
Blackadar, K-Theory for Operator Algebras, second edition (1998), 13.5.1
and the following paragraph describing F tensor 1. Allowing different
first-factor carriers is the rectangular version of the same formula.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uF₁ uG₁ uE₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
variable [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁]
variable {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
variable [SMul B₁ᵐᵒᵖ F₁] [CStarModule B₁ᵐᵒᵖ F₁]

section Raw

variable {E₂ : Type uE₂} [AddCommGroup E₂] [Module ℂ E₂]

/--
Let B₁ be a possibly nonunital complex C*-algebra with a partial order on B₁ᵐᵒᵖ. Let E₁ and F₁
be normed right inner-product B₁-modules with compatible complex normed-space structures, and
let E₂ be a complex vector space.

For an adjointable L : E₁ → F₁, tensoring its forward map with the identity defines a
complex-linear map E₁ ⊗[ℂ] E₂ → F₁ ⊗[ℂ] E₂.
-/
def rawLeftMap (L : AdjointableOperator B₁ E₁ F₁) :
    AlgebraicTensor E₁ E₂ →ₗ[ℂ] AlgebraicTensor F₁ E₂ :=
  TensorProduct.map L.toContinuousLinearMap.toLinearMap LinearMap.id

/--
Let B₁ be a possibly nonunital complex C*-algebra with a partial order on B₁ᵐᵒᵖ. Let E₁ and F₁
be normed right inner-product B₁-modules with compatible complex normed-space structures, and
let E₂ be a complex vector space.

For an adjointable L : E₁ → F₁ and x ∈ E₁, y ∈ E₂, the induced algebraic map sends x ⊗ y to Lx ⊗
y.
-/
@[simp]
theorem rawLeftMap_tmul (L : AdjointableOperator B₁ E₁ F₁)
    (x : E₁) (y : E₂) :
    rawLeftMap L (x ⊗ₜ[ℂ] y) = (L x) ⊗ₜ[ℂ] y := by
  simp only [rawLeftMap, TensorProduct.map_tmul, LinearMap.id_apply,
    ContinuousLinearMap.coe_coe, AdjointableOperator.coe_toContinuousLinearMap]

end Raw

variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
variable [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

The algebraic map induced by an adjointable L : E₁ → F₁ sends the coefficient-balancing
submodule for E₁ into the corresponding submodule for F₁.
-/
theorem balancingSpan_rawLeftMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) :
    balancingSpan (E₁ := E₁) φ ≤
      (balancingSpan (E₁ := F₁) φ).comap (rawLeftMap (E₂ := E₂) L) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨x, b, y⟩, rfl⟩
  change rawLeftMap L (balanceRelation φ x b y) ∈ balancingSpan (E₁ := F₁) φ
  simpa only [balanceRelation, map_sub, rawLeftMap_tmul,
    AdjointableOperator.map_right_smul] using balanceRelation_mem φ (L x) b y

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

For an adjointable L : E₁ → F₁ and algebraic tensors z ∈ E₁ ⊗[ℂ] E₂, w ∈ F₁ ⊗[ℂ] E₂, the Gram
forms satisfy ⟨(L ⊗ id)z,w⟩ = ⟨z,(L* ⊗ id)w⟩.
-/
theorem rawLeftMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁)
    (z : AlgebraicTensor E₁ E₂) (w : AlgebraicTensor F₁ E₂) :
    rawInner φ (rawLeftMap L z) w =
      rawInner φ z (rawLeftMap L.adjointOperator w) := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      simp only [rawLeftMap_tmul, rawInner_tmul_tmul,
        AdjointableOperator.adjoint_inner, AdjointableOperator.adjointOperator_apply]
    | add w w' hw hw' =>
      simp only [map_add, hw, hw']
  | add z z' hz hz' =>
    simp only [map_add, LinearMap.add_apply, hz, hz']

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures.

For an adjointable L : E₁ → F₁, tensoring L with the identity commutes with the right B₂-action
on the second tensor factor.
-/
theorem rawLeftMap_rawRightSMul
    (L : AdjointableOperator B₁ E₁ F₁) (b : B₂)
    (z : AlgebraicTensor E₁ E₂) :
    rawLeftMap L (rawRightSMul b z) =
      rawRightSMul b (rawLeftMap L z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp only [rawRightSMul_tmul, rawLeftMap_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

An adjointable L : E₁ → F₁ induces a complex-linear map between the balanced algebraic tensor
products of E₁ and F₁ with E₂ along φ.
-/
def balancedLeftMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) :
    BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] BalancedTensor (E₁ := F₁) φ :=
  (balancingSpan (E₁ := E₁) φ).mapQ (balancingSpan (E₁ := F₁) φ)
    (rawLeftMap L) (balancingSpan_rawLeftMap φ L)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

For an adjointable L : E₁ → F₁ and an algebraic tensor z, the image of its balanced quotient
class is the balanced quotient class of (L ⊗ id)z.
-/
theorem balancedLeftMap_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (z : AlgebraicTensor E₁ E₂) :
    balancedLeftMap φ L ((balancingSpan (E₁ := E₁) φ).mkQ z) =
      (balancingSpan (E₁ := F₁) φ).mkQ (rawLeftMap L z) := by
  simp only [balancedLeftMap, Submodule.mkQ_apply, Submodule.mapQ_apply]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

For an adjointable L : E₁ → F₁ and x ∈ E₁, y ∈ E₂, the induced balanced map sends x ⊗φ y to Lx
⊗φ y.
-/
@[simp]
theorem balancedLeftMap_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (x : E₁) (y : E₂) :
    balancedLeftMap φ L (balancedPure φ x y) = balancedPure φ (L x) y := by
  simp only [balancedPure, balancedLeftMap_mkQ, rawLeftMap_tmul]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

The balanced tensor maps induced by an adjointable L : E₁ → F₁ and its adjoint satisfy the
adjoint identity for the descended Gram forms.
-/
theorem balancedLeftMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁)
    (z : BalancedTensor (E₁ := E₁) φ) (w : BalancedTensor (E₁ := F₁) φ) :
    balancedInner φ (balancedLeftMap φ L z) w =
      balancedInner φ z (balancedLeftMap φ L.adjointOperator w) := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (balancingSpan (E₁ := F₁) φ).mkQ_surjective w
  simpa only [balancedLeftMap_mkQ, balancedInner_mkQ_mkQ] using
    rawLeftMap_inner_adjoint φ L z w

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

The balanced tensor map induced by an adjointable L : E₁ → F₁ respects the right B₂-action.
-/
theorem balancedLeftMap_balancedRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (b : B₂)
    (z : BalancedTensor (E₁ := E₁) φ) :
    balancedLeftMap φ L (balancedRightSMul φ b z) =
      balancedRightSMul φ b (balancedLeftMap φ L z) := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  simpa only [balancedLeftMap_mkQ, balancedRightSMul_mkQ] using
    congrArg (balancingSpan (E₁ := F₁) φ).mkQ
      (rawLeftMap_rawRightSMul L b z)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

The balanced tensor map induced by an adjointable L : E₁ → F₁ sends the Gram radical for E₁ into
the Gram radical for F₁.
-/
theorem radicalSpace_balancedLeftMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) :
    radicalSpace (E₁ := E₁) φ ≤
      (radicalSpace (E₁ := F₁) φ).comap (balancedLeftMap φ L) := by
  intro z hz
  change balancedLeftMap φ L z ∈ radicalSpace (E₁ := F₁) φ
  apply (mem_radicalSpace_iff φ _).mpr
  intro w
  rw [balancedLeftMap_inner_adjoint]
  exact (mem_radicalSpace_iff φ z).mp hz _

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

An adjointable L : E₁ → F₁ induces a complex-linear map between the Gram-radical quotients of
the balanced tensor products with E₂.
-/
def radicalLeftMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) :
    RadicalTensor (E₁ := E₁) φ →ₗ[ℂ] RadicalTensor (E₁ := F₁) φ :=
  (radicalSpace (E₁ := E₁) φ).mapQ (radicalSpace (E₁ := F₁) φ)
    (balancedLeftMap φ L) (radicalSpace_balancedLeftMap φ L)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

For an adjointable L : E₁ → F₁ and a balanced tensor z, the image of its radical quotient class
is the radical quotient class of its balanced image under L.
-/
theorem radicalLeftMap_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (z : BalancedTensor (E₁ := E₁) φ) :
    radicalLeftMap φ L ((radicalSpace (E₁ := E₁) φ).mkQ z) =
      (radicalSpace (E₁ := F₁) φ).mkQ (balancedLeftMap φ L z) := by
  simp only [radicalLeftMap, Submodule.mkQ_apply, Submodule.mapQ_apply]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

For an adjointable L : E₁ → F₁, the induced radical quotient map sends the class of x ⊗φ y to
the class of Lx ⊗φ y.
-/
theorem radicalLeftMap_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (x : E₁) (y : E₂) :
    radicalLeftMap φ L
        ((radicalSpace (E₁ := E₁) φ).mkQ (balancedPure φ x y)) =
      (radicalSpace (E₁ := F₁) φ).mkQ (balancedPure φ (L x) y) := by
  simp only [radicalLeftMap_mkQ, balancedLeftMap_pure]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

The radical quotient maps induced by an adjointable L : E₁ → F₁ and its adjoint satisfy the
adjoint identity for the descended coefficient-valued forms.
-/
theorem radicalLeftMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁)
    (z : RadicalTensor (E₁ := E₁) φ) (w : RadicalTensor (E₁ := F₁) φ) :
    radicalInner φ (radicalLeftMap φ L z) w =
      radicalInner φ z (radicalLeftMap φ L.adjointOperator w) := by
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := F₁) φ).mkQ_surjective w
  simpa only [radicalLeftMap_mkQ, radicalInner_mkQ_mkQ] using
    balancedLeftMap_inner_adjoint φ L z w

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

The radical quotient map induced by an adjointable L : E₁ → F₁ respects the right B₂-action.
-/
theorem radicalLeftMap_radicalRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (L : AdjointableOperator B₁ E₁ F₁) (b : B₂)
    (z : RadicalTensor (E₁ := E₁) φ) :
    radicalLeftMap φ L (radicalRightSMul φ b z) =
      radicalRightSMul φ b (radicalLeftMap φ L z) := by
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective z
  simpa only [radicalLeftMap_mkQ, radicalRightSMul_mkQ] using
    congrArg (radicalSpace (E₁ := F₁) φ).mkQ
      (balancedLeftMap_balancedRightSMul φ L b z)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ be a normed right inner-product B₁-module and E₂ a normed right inner-product
B₂-module, all with compatible complex normed-space structures. Let φ be a nonunital complex
star representation of B₁ by adjointable endomorphisms of E₂.

The identity on E₁ induces the identity on its balanced tensor Gram-radical quotient.
-/
@[simp]
theorem radicalLeftMap_id
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    radicalLeftMap (E₁ := E₁) φ AdjointableOperator.id = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [radicalLeftMap_mkQ, balancedLeftMap_mkQ, rawLeftMap_tmul,
      AdjointableOperator.id_apply, LinearMap.id_apply]
  | add z w hz hw =>
    simp only [map_add, LinearMap.id_apply, hz, hw]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁, F₁ and G₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

For adjointable L : E₁ → F₁ and S : F₁ → G₁, the radical quotient map of S ∘ L is the composite
of the two induced radical quotient maps.
-/
theorem radicalLeftMap_comp
    {G₁ : Type uG₁} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [SMul B₁ᵐᵒᵖ G₁] [CStarModule B₁ᵐᵒᵖ G₁]
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator B₁ F₁ G₁) (L : AdjointableOperator B₁ E₁ F₁) :
    radicalLeftMap φ (S.comp L) =
      (radicalLeftMap φ S).comp (radicalLeftMap φ L) := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [radicalLeftMap_mkQ, balancedLeftMap_mkQ, rawLeftMap_tmul,
      LinearMap.comp_apply, AdjointableOperator.comp_apply]
  | add z w hz hw =>
    simp only [map_add, LinearMap.comp_apply, hz, hw]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras with partial orders on their opposite
algebras. Let E₁ and F₁ be normed right inner-product B₁-modules and E₂ a normed right
inner-product B₂-module, all with compatible complex normed-space structures. Let φ be a
nonunital complex star representation of B₁ by adjointable endomorphisms of E₂.

The zero adjointable map E₁ → F₁ induces the zero map on the corresponding Gram-radical
quotients.
-/
@[simp]
theorem radicalLeftMap_zero
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    radicalLeftMap φ (0 : AdjointableOperator B₁ E₁ F₁) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [radicalLeftMap_mkQ, balancedLeftMap_mkQ, rawLeftMap_tmul,
      AdjointableOperator.zero_apply, TensorProduct.zero_tmul, map_zero,
      LinearMap.zero_apply]
  | add z w hz hw =>
    simp only [map_add, LinearMap.zero_apply, hz, hw, zero_add]

end CStarModule.InternalTensorProduct
