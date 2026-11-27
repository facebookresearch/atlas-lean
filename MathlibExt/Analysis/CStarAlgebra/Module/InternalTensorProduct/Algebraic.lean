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

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Balanced algebraic tensors of right C-star modules

The carrier is the ordinary complex algebraic tensor divided by the complex
span of the actual nonunital coefficient-balancing relations. Its right
coefficient action and coefficient-valued sesquilinear form are constructed
from the given modules and representation.

No norm, positive-form theorem, null quotient, completion or completed-model
witness is installed. The source is the algebraic prefix of Blackadar13.5.1;
the first inner-product slot is conjugate-linear.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂ uI uJ

/--
Let E₁ and E₂ be complex vector spaces.

The algebraic tensor product E₁ ⊗[ℂ] E₂ is the ordinary complex tensor product of these vector
spaces.
-/
abbrev AlgebraicTensor
    (E₁ : Type uE₁) (E₂ : Type uE₂)
    [AddCommGroup E₁] [Module ℂ E₁]
    [AddCommGroup E₂] [Module ℂ E₂] :=
  E₁ ⊗[ℂ] E₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [AddCommGroup E₁] [Module ℂ E₁] [Norm E₁]
variable [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
variable [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂]

local notation "T" => AlgebraicTensor E₁ E₂

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

For x ∈ E₁, b ∈ B₁ and y ∈ E₂, the balancing relation is (xb) ⊗ y − x ⊗ φ(b)y.
-/
def balanceRelation
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (b : B₁) (y : E₂) : T :=
  (x <• b) ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] (φ b y)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

The balancing submodule is the complex-linear span of all relations (xb) ⊗ y − x ⊗ φ(b)y.
-/
def balancingSpan
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) : Submodule ℂ T :=
  Submodule.span ℂ
    (Set.range fun p : E₁ × B₁ × E₂ => balanceRelation φ p.1 p.2.1 p.2.2)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

The balanced algebraic tensor product is the quotient of E₁ ⊗[ℂ] E₂ by the complex span of the
coefficient-balancing relations.
-/
abbrev BalancedTensor
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :=
  T ⧸ balancingSpan (E₁ := E₁) φ

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

The balanced pure tensor associated to x ∈ E₁ and y ∈ E₂ is the quotient class of x ⊗ y.
-/
def balancedPure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (y : E₂) : BalancedTensor (E₁ := E₁) φ :=
  (balancingSpan (E₁ := E₁) φ).mkQ (x ⊗ₜ[ℂ] y)

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

Every relation (xb) ⊗ y − x ⊗ φ(b)y belongs to the balancing submodule.
-/
theorem balanceRelation_mem
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (b : B₁) (y : E₂) :
    balanceRelation φ x b y ∈ balancingSpan (E₁ := E₁) φ :=
  Submodule.subset_span ⟨(x, b, y), rfl⟩

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
@[simp]
theorem balancedPure_add_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x x' : E₁) (y : E₂) :
    balancedPure φ (x + x') y = balancedPure φ x y + balancedPure φ x' y := by
  simp only [balancedPure, TensorProduct.add_tmul, map_add]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
@[simp]
theorem balancedPure_add_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (y y' : E₂) :
    balancedPure φ x (y + y') = balancedPure φ x y + balancedPure φ x y' := by
  simp only [balancedPure, TensorProduct.tmul_add, map_add]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
@[simp]
theorem balancedPure_smul_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (c : ℂ) (x : E₁) (y : E₂) :
    balancedPure φ (c • x) y = c • balancedPure φ x y := by
  simp only [balancedPure, ← TensorProduct.smul_tmul', map_smul]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
@[simp]
theorem balancedPure_smul_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (c : ℂ) (x : E₁) (y : E₂) :
    balancedPure φ x (c • y) = c • balancedPure φ x y := by
  simp only [balancedPure, TensorProduct.tmul_smul, map_smul]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
@[simp]
theorem balancedPure_zero_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (y : E₂) :
    balancedPure φ (0 : E₁) y = 0 := by
  simp only [balancedPure, TensorProduct.zero_tmul, map_zero]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
@[simp]
theorem balancedPure_zero_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (x : E₁) :
    balancedPure φ x (0 : E₂) = 0 := by
  simp only [balancedPure, TensorProduct.tmul_zero, map_zero]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

The balanced pure tensors satisfy (xb) ⊗φ y = x ⊗φ φ(b)y for x ∈ E₁, b ∈ B₁ and y ∈ E₂.
-/
@[simp]
theorem balancedPure_balance
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (b : B₁) (y : E₂) :
    balancedPure φ (x <• b) y = balancedPure φ x (φ b y) := by
  change (Submodule.Quotient.mk ((x <• b) ⊗ₜ[ℂ] y) :
    BalancedTensor (E₁ := E₁) φ) = Submodule.Quotient.mk (x ⊗ₜ[ℂ] (φ b y))
  apply (Submodule.Quotient.eq (balancingSpan (E₁ := E₁) φ)).2
  exact balanceRelation_mem φ x b y

/--
Let E₁ be a complex vector space. Let B₂ be a possibly nonunital complex C*-algebra with a
partial order on B₂ᵐᵒᵖ, and let E₂ be a normed right inner-product B₂-module with a compatible
complex normed-space structure.

For b ∈ B₂, the right coefficient action on the algebraic tensor is the complex-linear map x ⊗ y
↦ x ⊗ (yb).
-/
def rawRightSMul (b : B₂) : T →ₗ[ℂ] T :=
  TensorProduct.map LinearMap.id
    ((CStarModule.rightSMulLinear (B := B₂) (E := E₂)).flip b)

omit [Norm E₁] in
@[simp]
theorem rawRightSMul_tmul (b : B₂) (x : E₁) (y : E₂) :
    rawRightSMul (E₁ := E₁) b (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (y <• b) := by
  simp only [rawRightSMul, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.flip_apply, CStarModule.rightSMulLinear_apply]

omit [Norm E₁] in
theorem rawRightSMul_zero :
    rawRightSMul (E₁ := E₁) (E₂ := E₂) (0 : B₂) = 0 := by
  apply TensorProduct.ext'
  intro x y
  simp only [rawRightSMul_tmul, CStarModule.right_smul_zero,
    TensorProduct.tmul_zero, LinearMap.zero_apply]

omit [Norm E₁] in
theorem rawRightSMul_add (b c : B₂) :
    rawRightSMul (E₁ := E₁) (E₂ := E₂) (b + c) =
      rawRightSMul b + rawRightSMul c := by
  apply TensorProduct.ext'
  intro x y
  simp only [rawRightSMul_tmul, CStarModule.right_smul_add,
    TensorProduct.tmul_add, LinearMap.add_apply]

omit [Norm E₁] in
/--
Let E₁ be a complex vector space. Let B₂ be a possibly nonunital complex C*-algebra with a
partial order on B₂ᵐᵒᵖ, and let E₂ be a normed right inner-product B₂-module with a compatible
complex normed-space structure.

On E₁ ⊗[ℂ] E₂, acting by bc ∈ B₂ equals acting first by b and then by c.
-/
theorem rawRightSMul_mul (b c : B₂) :
    rawRightSMul (E₁ := E₁) (E₂ := E₂) (b * c) =
      (rawRightSMul c).comp (rawRightSMul b) := by
  apply TensorProduct.ext'
  intro x y
  simp only [rawRightSMul_tmul, LinearMap.comp_apply, CStarModule.right_smul_mul]

omit [Norm E₁] in
theorem rawRightSMul_smul (c : ℂ) (b : B₂) :
    rawRightSMul (E₁ := E₁) (E₂ := E₂) (c • b) = c • rawRightSMul b := by
  apply TensorProduct.ext'
  intro x y
  simp only [rawRightSMul_tmul, CStarModule.right_smul_smul,
    TensorProduct.tmul_smul, LinearMap.smul_apply]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

The right action of every b ∈ B₂ on the algebraic tensor preserves the coefficient-balancing
submodule.
-/
theorem balancingSpan_rawRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b : B₂) :
    balancingSpan (E₁ := E₁) φ ≤
      (balancingSpan (E₁ := E₁) φ).comap (rawRightSMul (E₁ := E₁) b) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨x, a, y⟩, rfl⟩
  change rawRightSMul b (balanceRelation φ x a y) ∈ balancingSpan φ
  simp only [balanceRelation, map_sub, rawRightSMul_tmul]
  simpa only [balanceRelation, AdjointableOperator.map_right_smul] using
    balanceRelation_mem φ x a (y <• b)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

The right action of b ∈ B₂ descends to a complex-linear map on the balanced algebraic tensor
product.
-/
def balancedRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b : B₂) :
    BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] BalancedTensor (E₁ := E₁) φ :=
  (balancingSpan (E₁ := E₁) φ).mapQ (balancingSpan φ)
    (rawRightSMul b) (balancingSpan_rawRightSMul φ b)

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
theorem balancedRightSMul_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (b : B₂) (z : T) :
    balancedRightSMul φ b ((balancingSpan φ).mkQ z) =
      (balancingSpan φ).mkQ (rawRightSMul b z) := by
  simp only [balancedRightSMul, Submodule.mkQ_apply, Submodule.mapQ_apply]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
@[simp]
theorem balancedRightSMul_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (b : B₂) (x : E₁) (y : E₂) :
    balancedRightSMul φ b (balancedPure φ x y) =
      balancedPure φ x (y <• b) := by
  simp only [balancedPure, balancedRightSMul_mkQ, rawRightSMul_tmul]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
theorem balancedRightSMul_zero
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    balancedRightSMul (E₁ := E₁) φ (0 : B₂) = 0 := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
  simp only [balancedRightSMul_mkQ, rawRightSMul_zero,
    LinearMap.zero_apply, map_zero]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
theorem balancedRightSMul_add
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b c : B₂) :
    balancedRightSMul (E₁ := E₁) φ (b + c) =
      balancedRightSMul φ b + balancedRightSMul φ c := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
  simp only [balancedRightSMul_mkQ, rawRightSMul_add, LinearMap.add_apply, map_add]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
theorem balancedRightSMul_mul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (b c : B₂) :
    balancedRightSMul (E₁ := E₁) φ (b * c) =
      (balancedRightSMul φ c).comp (balancedRightSMul φ b) := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
  simp only [balancedRightSMul_mkQ, rawRightSMul_mul, LinearMap.comp_apply]

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
theorem balancedRightSMul_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (c : ℂ) (b : B₂) :
    balancedRightSMul (E₁ := E₁) φ (c • b) = c • balancedRightSMul φ b := by
  apply LinearMap.ext
  intro q
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
  simp only [balancedRightSMul_mkQ, rawRightSMul_smul, LinearMap.smul_apply, map_smul]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

The balanced algebraic tensor product carries a right B₂-action induced by right multiplication
on its second tensor factor.
-/
@[instance_reducible]
def balancedRightAction
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    SMul B₂ᵐᵒᵖ (BalancedTensor (E₁ := E₁) φ) where
  smul b q := balancedRightSMul φ b.unop q

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

For x ∈ E₁, y ∈ E₂ and b ∈ B₂, balanced pure tensors satisfy x ⊗φ (yb) = (x ⊗φ y)b.
-/
theorem balancedPure_right_smul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (y : E₂) (b : B₂) :
    letI : SMul B₂ᵐᵒᵖ (BalancedTensor (E₁ := E₁) φ) := balancedRightAction φ;
    balancedPure φ x (y <• b) = balancedPure φ x y <• b := by
  change balancedPure φ x (y <• b) =
    balancedRightSMul φ b (balancedPure φ x y)
  exact (balancedRightSMul_pure φ b x y).symm

private def pureRightGram
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (u : E₂) : T →ₗ[ℂ] B₂ :=
  TensorProduct.lift
    { toFun := fun y =>
        { toFun := fun v => rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v)
          map_add' := by
            intro v w
            simp only [map_add, rightInner_add_right]
          map_smul' := by
            intro c v
            simp only [map_smul, rightInner_smul_right, RingHom.id_apply] }
      map_add' := by
        intro y z
        apply LinearMap.ext
        intro v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, rightInner_add_right, map_add,
          AdjointableOperator.add_apply, rightInner_add_right, LinearMap.add_apply]
      map_smul' := by
        intro c y
        apply LinearMap.ext
        intro v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, rightInner_smul_right, map_smul,
          AdjointableOperator.smul_apply, rightInner_smul_right, LinearMap.smul_apply,
          RingHom.id_apply] }

private theorem pureRightGram_tmul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x y : E₁) (u v : E₂) :
    pureRightGram φ x u (y ⊗ₜ[ℂ] v) =
      rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v) := by
  simp only [pureRightGram, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]

private def pureGramLeft
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    E₁ →ₗ⋆[ℂ] E₂ →ₗ⋆[ℂ] T →ₗ[ℂ] B₂ where
  toFun x :=
    { toFun := fun u => pureRightGram φ x u
      map_add' := by
        intro u v
        apply TensorProduct.ext'
        intro y w
        simp only [pureRightGram_tmul, rightInner_add_left, LinearMap.add_apply]
      map_smul' := by
        intro c u
        apply TensorProduct.ext'
        intro y v
        simp only [pureRightGram_tmul, rightInner_smul_left,
          LinearMap.smul_apply, starRingEnd_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro u
    apply TensorProduct.ext'
    intro z v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, pureRightGram_tmul,
      rightInner_add_left, map_add, AdjointableOperator.add_apply,
      rightInner_add_right, LinearMap.add_apply]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro u
    apply TensorProduct.ext'
    intro y v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, pureRightGram_tmul,
      rightInner_smul_left, map_smul, AdjointableOperator.smul_apply,
      rightInner_smul_right, LinearMap.smul_apply, starRingEnd_apply]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

The B₂-valued Gram form on E₁ ⊗[ℂ] E₂ is sesquilinear and is determined on pure tensors by ⟨x ⊗
u, y ⊗ v⟩ = ⟨u, φ(⟨x,y⟩)v⟩.
-/
@[no_expose]
def rawInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    T →ₗ⋆[ℂ] T →ₗ[ℂ] B₂ :=
  TensorProduct.lift (pureGramLeft φ)

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

For x, y ∈ E₁ and u, v ∈ E₂, the Gram form of the pure tensors is ⟨x ⊗ u, y ⊗ v⟩ = ⟨u,
φ(⟨x,y⟩)v⟩.
-/
@[simp]
theorem rawInner_tmul_tmul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x y : E₁) (u v : E₂) :
    rawInner φ (x ⊗ₜ[ℂ] u) (y ⊗ₜ[ℂ] v) =
      rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v) := by
  simpa only [rawInner, TensorProduct.lift.tmul, pureGramLeft,
    LinearMap.coe_mk, AddHom.coe_mk] using pureRightGram_tmul φ x y u v

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

For arbitrary finite index sets I and J, the Gram form of ∑ᵢ xᵢ ⊗ uᵢ and ∑ⱼ yⱼ ⊗ vⱼ equals ∑ᵢ ∑ⱼ
⟨uᵢ, φ(⟨xᵢ,yⱼ⟩)vⱼ⟩.
-/
theorem rawInner_sum_tmul_sum_tmul
    {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : I → E₁) (u : I → E₂) (y : J → E₁) (v : J → E₂) :
    rawInner φ (∑ i, (x i) ⊗ₜ[ℂ] (u i))
        (∑ j, (y j) ⊗ₜ[ℂ] (v j)) =
      ∑ i, ∑ j, rightInner (B := B₂) (u i)
        (φ (rightInner (B := B₁) (x i) (y j)) (v j)) := by
  simp only [map_sum, LinearMap.sum_apply, rawInner_tmul_tmul]
  exact Finset.sum_comm

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

For algebraic tensors z and w, the B₂-valued Gram form satisfies star(⟨z,w⟩) = ⟨w,z⟩.
-/
theorem star_rawInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (z w : T) :
    star (rawInner φ z w) = rawInner φ w z := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      rw [rawInner_tmul_tmul, rawInner_tmul_tmul, star_rightInner,
        AdjointableOperator.adjoint_inner]
      simp only [← AdjointableOperator.star_apply, ← map_star, star_rightInner]
    | add w w' hw hw' =>
      simp only [map_add, LinearMap.add_apply, star_add, hw, hw']
  | add z z' hz hz' =>
    simp only [map_add, LinearMap.add_apply, star_add, hz, hz']

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

For algebraic tensors z and w and b ∈ B₂, the Gram form satisfies ⟨z, wb⟩ = ⟨z,w⟩b.
-/
theorem rawInner_rawRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w : T) (b : B₂) :
    rawInner φ z (rawRightSMul b w) = rawInner φ z w * b := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      rw [rawRightSMul_tmul, rawInner_tmul_tmul,
        AdjointableOperator.map_right_smul, rightInner_right_smul, rawInner_tmul_tmul]
    | add w w' hw hw' =>
      simp only [map_add, hw, hw', add_mul]
  | add z z' hz hz' =>
    simp only [map_add, LinearMap.add_apply, hz, hz', add_mul]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

The Gram form vanishes when a coefficient-balancing relation is placed in its second argument.
-/
theorem rawInner_balanceRelation_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z : T) (x : E₁) (b : B₁) (y : E₂) :
    rawInner φ z (balanceRelation φ x b y) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul z u =>
    simp only [balanceRelation, map_sub, rawInner_tmul_tmul,
      rightInner_right_smul, map_mul, AdjointableOperator.mul_apply, sub_self]
  | add z z' hz hz' =>
    simp only [map_add, LinearMap.add_apply, hz, hz', add_zero]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

The Gram form vanishes when a coefficient-balancing relation is placed in its first argument.
-/
theorem rawInner_balanceRelation_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : E₁) (b : B₁) (y : E₂) (z : T) :
    rawInner φ (balanceRelation φ x b y) z = 0 := by
  apply star_injective
  simpa only [star_rawInner, star_zero] using
    rawInner_balanceRelation_right φ z x b y

private theorem balancingSpan_le_ker_rawInner_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (z : T) :
    balancingSpan (E₁ := E₁) φ ≤ LinearMap.ker (rawInner φ z) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨x, b, y⟩, rfl⟩
  change rawInner φ z (balanceRelation φ x b y) = 0
  exact rawInner_balanceRelation_right φ z x b y

private theorem balancingSpan_le_ker_rawInner_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    balancingSpan (E₁ := E₁) φ ≤ LinearMap.ker (rawInner φ) := by
  intro z hz
  change rawInner φ z = 0
  apply LinearMap.ext
  intro w
  apply star_injective
  have h : rawInner φ w z = 0 :=
    balancingSpan_le_ker_rawInner_right φ w hz
  simpa only [star_rawInner, LinearMap.zero_apply, star_zero] using h

private def rightQuotientInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    T →ₗ⋆[ℂ] BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] B₂ where
  toFun z := (balancingSpan (E₁ := E₁) φ).liftQ (rawInner φ z)
    (balancingSpan_le_ker_rawInner_right φ z)
  map_add' := by
    intro z w
    apply LinearMap.ext
    intro q
    obtain ⟨u, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
    simpa only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.add_apply] using
      congrArg (fun L : T →ₗ[ℂ] B₂ => L u) ((rawInner φ).map_add z w)
  map_smul' := by
    intro c z
    apply LinearMap.ext
    intro q
    obtain ⟨u, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
    simpa only [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply] using
      congrArg (fun L : T →ₗ[ℂ] B₂ => L u) ((rawInner φ).map_smulₛₗ c z)

private theorem balancingSpan_le_ker_rightQuotientInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    balancingSpan (E₁ := E₁) φ ≤ LinearMap.ker (rightQuotientInner φ) := by
  intro z hz
  change rightQuotientInner φ z = 0
  apply LinearMap.ext
  intro q
  obtain ⟨w, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
  change rawInner φ z w = 0
  have h : rawInner φ z = 0 := balancingSpan_le_ker_rawInner_left φ hz
  simpa only [LinearMap.zero_apply] using
    congrArg (fun L : T →ₗ[ℂ] B₂ => L w) h

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

The B₂-valued Gram form descends to a sesquilinear form on the balanced algebraic tensor
product, conjugate-linear in its first argument and linear in its second.
-/
@[no_expose]
def balancedInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    BalancedTensor (E₁ := E₁) φ →ₗ⋆[ℂ]
      BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] B₂ :=
  (balancingSpan (E₁ := E₁) φ).liftQ (rightQuotientInner φ)
    (balancingSpan_le_ker_rightQuotientInner φ)

theorem balancedInner_mkQ_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) (z w : T) :
    balancedInner φ ((balancingSpan φ).mkQ z) ((balancingSpan φ).mkQ w) =
      rawInner φ z w := by
  simp only [balancedInner, Submodule.mkQ_apply, Submodule.liftQ_apply,
    rightQuotientInner, LinearMap.coe_mk, AddHom.coe_mk]

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

For balanced pure tensors, the Gram form is ⟨x ⊗φ u, y ⊗φ v⟩ = ⟨u, φ(⟨x,y⟩)v⟩.
-/
@[simp]
theorem balancedInner_pure_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x y : E₁) (u v : E₂) :
    balancedInner φ (balancedPure φ x u) (balancedPure φ y v) =
      rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v) := by
  simp only [balancedPure, balancedInner_mkQ_mkQ, rawInner_tmul_tmul]

theorem star_balancedInner
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w : BalancedTensor (E₁ := E₁) φ) :
    star (balancedInner φ z w) = balancedInner φ w z := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective w
  simpa only [balancedInner_mkQ_mkQ] using star_rawInner φ z w

theorem balancedInner_add_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w v : BalancedTensor (E₁ := E₁) φ) :
    balancedInner φ (z + w) v = balancedInner φ z v + balancedInner φ w v := by
  simpa only [LinearMap.add_apply] using
    congrArg (fun L => L v) ((balancedInner φ).map_add z w)

theorem balancedInner_add_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w v : BalancedTensor (E₁ := E₁) φ) :
    balancedInner φ z (w + v) = balancedInner φ z w + balancedInner φ z v :=
  (balancedInner φ z).map_add w v

theorem balancedInner_smul_left
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (c : ℂ) (z w : BalancedTensor (E₁ := E₁) φ) :
    balancedInner φ (c • z) w = star c • balancedInner φ z w := by
  simpa only [LinearMap.smul_apply, starRingEnd_apply] using
    congrArg (fun L => L w) ((balancedInner φ).map_smulₛₗ c z)

theorem balancedInner_smul_right
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (c : ℂ) (z w : BalancedTensor (E₁ := E₁) φ) :
    balancedInner φ z (c • w) = c • balancedInner φ z w :=
  (balancedInner φ z).map_smul c w

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

For balanced tensors z and w and b ∈ B₂, the descended Gram form satisfies ⟨z, wb⟩ = ⟨z,w⟩b.
-/
theorem balancedInner_balancedRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (z w : BalancedTensor (E₁ := E₁) φ) (b : B₂) :
    balancedInner φ z (balancedRightSMul φ b w) = balancedInner φ z w * b := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective w
  simpa only [balancedRightSMul_mkQ, balancedInner_mkQ_mkQ] using
    rawInner_rawRightSMul φ z w b

/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras, each with a partial order on its
opposite algebra. Let E₁ be a complex vector space with a norm and a right B₁-action satisfying
the inner-product C*-module laws. Let E₂ be a normed right inner-product B₂-module with a
compatible complex normed-space structure. Let φ be a nonunital complex star representation of
B₁ by adjointable endomorphisms of E₂.

For arbitrary finite index sets I and J, the Gram form of ∑ᵢ xᵢ ⊗φ uᵢ and ∑ⱼ yⱼ ⊗φ vⱼ equals ∑ᵢ
∑ⱼ ⟨uᵢ, φ(⟨xᵢ,yⱼ⟩)vⱼ⟩, including when either index set is empty.
-/
theorem balancedInner_sum_pure_sum_pure
    {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (x : I → E₁) (u : I → E₂) (y : J → E₁) (v : J → E₂) :
    balancedInner φ (∑ i, balancedPure φ (x i) (u i))
        (∑ j, balancedPure φ (y j) (v j)) =
      ∑ i, ∑ j, rightInner (B := B₂) (u i)
        (φ (rightInner (B := B₁) (x i) (y j)) (v j)) := by
  simp only [map_sum, LinearMap.sum_apply, balancedInner_pure_pure]
  exact Finset.sum_comm

omit [PartialOrder B₁ᵐᵒᵖ] [Norm E₁] [CStarModule B₁ᵐᵒᵖ E₁] in
/--
Let B₁ and B₂ be possibly nonunital complex C*-algebras. Let E₁ be a complex vector space with a
right B₁-action, and let E₂ be a normed right inner-product B₂-module with a compatible complex
normed-space structure and a partial order on B₂ᵐᵒᵖ. Let φ be a nonunital complex star
representation of B₁ by adjointable endomorphisms of E₂.

The balanced pure tensors have complex-linear span equal to the entire balanced algebraic tensor
product.
-/
theorem balancedPure_span_eq_top
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂) :
    Submodule.span ℂ (Set.range fun p : E₁ × E₂ => balancedPure φ p.1 p.2) = ⊤ := by
  apply top_unique
  intro q hq
  clear hq
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective q
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact Submodule.subset_span ⟨(x, y), rfl⟩
  | add z w hz hw =>
    simpa only [map_add] using Submodule.add_mem _ hz hw

end CStarModule.InternalTensorProduct
