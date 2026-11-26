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
# Commuting right-factor maps of internal tensors

For right pre-Hilbert modules `E₁,E₂` over nonunital `B₁,B₂` and a complex nonunital star
representation `φ : B₁ → End_(B₂)(E₂)`, the internal tensor balances `(x <• b)⊗y = x⊗φ(b)y`. Its
coefficient inner product is `⟨x⊗y,x'⊗y'⟩_(B₂) = ⟨y,φ(⟨x,x'⟩_(B₁))y'⟩_(B₂)`.

An adjointable `S` on `E₂` commuting with every `φ(b)` induces `I⊗S` on the complex algebraic
tensor, balanced quotient and zero-inner-product radical quotient. The adjoint is induced by
`S*`, and these maps preserve right `B₂` actions. The algebraic constructions do not require
complete component modules.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂]

/-- **Right factor on the complex algebraic tensor.** For a complex vector space `E₁`, a right
pre-Hilbert module `E₂` over nonunital C-star `B₂`, and an adjointable `S : E₂ → E₂`, the
complex-linear map `rawRightFactorMap S` is `I⊗S`, sending `x⊗y` to `x⊗S y`. -/
def rawRightFactorMap (S : AdjointableOperator.End B₂ E₂) :
    AlgebraicTensor E₁ E₂ →ₗ[ℂ] AlgebraicTensor E₁ E₂ :=
  TensorProduct.map LinearMap.id S.toContinuousLinearMap.toLinearMap

/-- **Right-factor map on a pure tensor.** For `x : E₁`, `y : E₂` and adjointable `S`,
`rawRightFactorMap S (x⊗y) = x⊗S y`. -/
@[simp]
theorem rawRightFactorMap_tmul (S : AdjointableOperator.End B₂ E₂)
    (x : E₁) (y : E₂) :
    rawRightFactorMap S (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (S y) := by
  simp only [rawRightFactorMap, TensorProduct.map_tmul, LinearMap.id_apply,
    ContinuousLinearMap.coe_coe, AdjointableOperator.coe_toContinuousLinearMap]

omit [PartialOrder B₁ᵐᵒᵖ] in
/-- **Adjoints in a representation commutant.** For a complex nonunital star representation `φ` on
a right module and adjointable `S`, if `S` commutes with every `φ(b)`, then
`S.adjointOperator` also commutes with every `φ(b)`. -/
theorem rightFactorCommutant_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    ∀ b : B₁, Commute S.adjointOperator (φ b) := by
  intro b
  change Commute (star S) (φ b)
  simpa only [map_star, star_star] using (hComm (star b)).star_star

omit [PartialOrder B₁ᵐᵒᵖ] in
private theorem rightFactorCommutant_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (b : B₁) (y : E₂) :
    S (φ b y) = φ b (S y) := by
  simpa only [AdjointableOperator.mul_apply] using
    congrArg (fun T : AdjointableOperator.End B₂ E₂ => T y) (hComm b).eq

omit [PartialOrder B₁ᵐᵒᵖ] [CStarModule B₁ᵐᵒᵖ E₁] in
/-- **Preservation of the balancing relations.** Let `E₁,E₂` be right pre-Hilbert modules over
nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)`
be a complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting
with every `φ(b)`. `I⊗S` maps the complex span of `(x <• b)⊗y - x⊗φ(b)y` into itself. -/
theorem balancingSpan_rawRightFactorMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    balancingSpan (E₁ := E₁) φ ≤
      (balancingSpan (E₁ := E₁) φ).comap (rawRightFactorMap S) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨x, b, y⟩, rfl⟩
  change rawRightFactorMap S (balanceRelation φ x b y) ∈ balancingSpan (E₁ := E₁) φ
  simpa only [balanceRelation, map_sub, rawRightFactorMap_tmul,
    rightFactorCommutant_apply φ S hComm] using balanceRelation_mem φ x b (S y)

/-- **Adjoint pairing on the raw tensor.** Let `E₁,E₂` be right pre-Hilbert modules over nonunital
C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)` be a
complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting with
every `φ(b)`. for raw tensors `z,w`, `rawInner φ ((I⊗S) z) w = rawInner φ z ((I⊗S*) w)`. -/
theorem rawRightFactorMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b))
    (z w : AlgebraicTensor E₁ E₂) :
    rawInner φ (rawRightFactorMap S z) w =
      rawInner φ z (rawRightFactorMap S.adjointOperator w) := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      simp only [rawRightFactorMap_tmul, rawInner_tmul_tmul,
        AdjointableOperator.adjoint_inner]
      rw [← AdjointableOperator.adjointOperator_apply,
        rightFactorCommutant_apply φ S.adjointOperator
          (rightFactorCommutant_adjoint φ S hComm)]
    | add w w' hw hw' => simp only [map_add, hw, hw']
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']

/-- **Right coefficients commute with a tensor factor map.** For adjointable `S` on a right
`B₂`-module and a raw complex tensor `z`, `(I⊗S)(z <• b) = ((I⊗S)z) <• b` for every `b : B₂`. -/
theorem rawRightFactorMap_rawRightSMul
    (S : AdjointableOperator.End B₂ E₂) (b : B₂)
    (z : AlgebraicTensor E₁ E₂) :
    rawRightFactorMap S (rawRightSMul b z) =
      rawRightSMul b (rawRightFactorMap S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [rawRightSMul_tmul, rawRightFactorMap_tmul,
      AdjointableOperator.map_right_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- **Right factor on the balanced quotient.** Let `E₁,E₂` be right pre-Hilbert modules over
nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)`
be a complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting
with every `φ(b)`. `balancedRightFactorMap` is the descended complex-linear map `[x⊗y] ↦ [x⊗S
y]` on the quotient by the `B₁` balancing relations. -/
def balancedRightFactorMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] BalancedTensor (E₁ := E₁) φ :=
  (balancingSpan (E₁ := E₁) φ).mapQ (balancingSpan (E₁ := E₁) φ)
    (rawRightFactorMap S) (balancingSpan_rawRightFactorMap φ S hComm)

omit [PartialOrder B₁ᵐᵒᵖ] [CStarModule B₁ᵐᵒᵖ E₁] in
/-- **Balanced representative of a right-factor map.** Let `E₁,E₂` be right pre-Hilbert modules
over nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ →
End_(B₂)(E₂)` be a complex nonunital star homomorphism and `S` an adjointable endomorphism of
`E₂` commuting with every `φ(b)`. the quotient map `q_bal` satisfies `balancedRightFactorMap φ
S hComm (q_bal z) = q_bal (rawRightFactorMap S z)`. -/
theorem balancedRightFactorMap_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (z : AlgebraicTensor E₁ E₂) :
    balancedRightFactorMap φ S hComm ((balancingSpan (E₁ := E₁) φ).mkQ z) =
      (balancingSpan (E₁ := E₁) φ).mkQ (rawRightFactorMap S z) := by
  simp only [balancedRightFactorMap, Submodule.mkQ_apply, Submodule.mapQ_apply]

omit [PartialOrder B₁ᵐᵒᵖ] [CStarModule B₁ᵐᵒᵖ E₁] in
/-- **Right factor on balanced pure tensors.** Let `E₁,E₂` be right pre-Hilbert modules over
nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)`
be a complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting
with every `φ(b)`. `balancedRightFactorMap φ S hComm (balancedPure φ x y) = balancedPure φ x
(S y)`. -/
@[simp]
theorem balancedRightFactorMap_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (x : E₁) (y : E₂) :
    balancedRightFactorMap φ S hComm (balancedPure φ x y) =
      balancedPure φ x (S y) := by
  simp only [balancedPure, balancedRightFactorMap_mkQ, rawRightFactorMap_tmul]

/-- **Adjoint pairing after balancing.** Let `E₁,E₂` be right pre-Hilbert modules over nonunital
C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)` be a
complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting with
every `φ(b)`. for balanced `z,w`, `⟨R_S z,w⟩ = ⟨z,R_(S*) w⟩`, where `R_S =
balancedRightFactorMap φ S hComm`. -/
theorem balancedRightFactorMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b))
    (z w : BalancedTensor (E₁ := E₁) φ) :
    balancedInner φ (balancedRightFactorMap φ S hComm z) w =
      balancedInner φ z (balancedRightFactorMap φ S.adjointOperator
        (rightFactorCommutant_adjoint φ S hComm) w) := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective w
  simpa only [balancedRightFactorMap_mkQ, balancedInner_mkQ_mkQ] using
    rawRightFactorMap_inner_adjoint φ S hComm z w

omit [PartialOrder B₁ᵐᵒᵖ] [CStarModule B₁ᵐᵒᵖ E₁] in
/-- **Right action after balancing.** Let `E₁,E₂` be right pre-Hilbert modules over nonunital
C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)` be a
complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting with
every `φ(b)`. put `R_S = balancedRightFactorMap φ S hComm`. It satisfies `R_S(z <• b) = R_S(z)
<• b` for each `b : B₂`. -/
theorem balancedRightFactorMap_balancedRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (b : B₂)
    (z : BalancedTensor (E₁ := E₁) φ) :
    balancedRightFactorMap φ S hComm (balancedRightSMul φ b z) =
      balancedRightSMul φ b (balancedRightFactorMap φ S hComm z) := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  simpa only [balancedRightFactorMap_mkQ, balancedRightSMul_mkQ] using
    congrArg (balancingSpan (E₁ := E₁) φ).mkQ
      (rawRightFactorMap_rawRightSMul S b z)

/-- **Preservation of the zero-inner-product radical.** Let `E₁,E₂` be right pre-Hilbert modules
over nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ →
End_(B₂)(E₂)` be a complex nonunital star homomorphism and `S` an adjointable endomorphism of
`E₂` commuting with every `φ(b)`. the balanced map induced by `I⊗S` preserves the radical,
since its paired adjoint is induced by `I⊗S*`. -/
theorem radicalSpace_balancedRightFactorMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    radicalSpace (E₁ := E₁) φ ≤
      (radicalSpace (E₁ := E₁) φ).comap (balancedRightFactorMap φ S hComm) := by
  intro z hz
  change balancedRightFactorMap φ S hComm z ∈ radicalSpace (E₁ := E₁) φ
  apply (mem_radicalSpace_iff φ _).mpr
  intro w
  rw [balancedRightFactorMap_inner_adjoint]
  exact (mem_radicalSpace_iff φ z).mp hz _

/-- **Right factor on the radical quotient.** Let `E₁,E₂` be right pre-Hilbert modules over
nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)`
be a complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting
with every `φ(b)`. the complex-linear map on the balanced tensor modulo its radical is
determined by `[x⊗y] ↦ [x⊗S y]`. -/
def radicalRightFactorMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    RadicalTensor (E₁ := E₁) φ →ₗ[ℂ] RadicalTensor (E₁ := E₁) φ :=
  (radicalSpace (E₁ := E₁) φ).mapQ (radicalSpace (E₁ := E₁) φ)
    (balancedRightFactorMap φ S hComm) (radicalSpace_balancedRightFactorMap φ S hComm)

/-- **Radical representative of a right-factor map.** Let `E₁,E₂` be right pre-Hilbert modules
over nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ →
End_(B₂)(E₂)` be a complex nonunital star homomorphism and `S` an adjointable endomorphism of
`E₂` commuting with every `φ(b)`. the radical quotient map `q_rad` satisfies
`radicalRightFactorMap φ S hComm (q_rad z) = q_rad (balancedRightFactorMap φ S hComm z)`. -/
theorem radicalRightFactorMap_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (z : BalancedTensor (E₁ := E₁) φ) :
    radicalRightFactorMap φ S hComm ((radicalSpace (E₁ := E₁) φ).mkQ z) =
      (radicalSpace (E₁ := E₁) φ).mkQ (balancedRightFactorMap φ S hComm z) := by
  simp only [radicalRightFactorMap, Submodule.mkQ_apply, Submodule.mapQ_apply]

/-- **Right factor on radical pure tensors.** Let `E₁,E₂` be right pre-Hilbert modules over
nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)`
be a complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting
with every `φ(b)`. the radical class of `x⊗y` is sent to the radical class of `x⊗S y`. -/
theorem radicalRightFactorMap_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (x : E₁) (y : E₂) :
    radicalRightFactorMap φ S hComm ((radicalSpace (E₁ := E₁) φ).mkQ (balancedPure φ x y)) =
      (radicalSpace (E₁ := E₁) φ).mkQ (balancedPure φ x (S y)) := by
  simp only [radicalRightFactorMap_mkQ, balancedRightFactorMap_pure]

/-- **Adjoint pairing on the radical quotient.** Let `E₁,E₂` be right pre-Hilbert modules over
nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)`
be a complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting
with every `φ(b)`. put `R_S = radicalRightFactorMap φ S hComm`. Then `radicalInner φ (R_S z) w
= radicalInner φ z (R_(S*) w)`, using the induced map of `S*` on the right. -/
theorem radicalRightFactorMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b))
    (z w : RadicalTensor (E₁ := E₁) φ) :
    radicalInner φ (radicalRightFactorMap φ S hComm z) w =
      radicalInner φ z (radicalRightFactorMap φ S.adjointOperator
        (rightFactorCommutant_adjoint φ S hComm) w) := by
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective w
  simpa only [radicalRightFactorMap_mkQ, radicalInner_mkQ_mkQ] using
    balancedRightFactorMap_inner_adjoint φ S hComm z w

/-- **Right action on the radical quotient.** Let `E₁,E₂` be right pre-Hilbert modules over
nonunital C-star algebras `B₁,B₂` with their coefficient orders. Let `φ : B₁ → End_(B₂)(E₂)`
be a complex nonunital star homomorphism and `S` an adjointable endomorphism of `E₂` commuting
with every `φ(b)`. put `R_S = radicalRightFactorMap φ S hComm`. It commutes with the right
`B₂` action: `R_S(z <• b) = R_S(z) <• b`. -/
theorem radicalRightFactorMap_radicalRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (b : B₂)
    (z : RadicalTensor (E₁ := E₁) φ) :
    radicalRightFactorMap φ S hComm (radicalRightSMul φ b z) =
      radicalRightSMul φ b (radicalRightFactorMap φ S hComm z) := by
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective z
  simpa only [radicalRightFactorMap_mkQ, radicalRightSMul_mkQ] using
    congrArg (radicalSpace (E₁ := E₁) φ).mkQ
      (balancedRightFactorMap_balancedRightSMul φ S hComm b z)

end CStarModule.InternalTensorProduct
