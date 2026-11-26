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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.HilbertAction
public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.CoefficientHom
public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin

/-!
# Rank-one compacts on Hilbert amplification

For a complex Hilbert space `H`, the compact rank-one operator `θ_(ξ,η)` acts by `ζ ↦ ⟪η,ζ⟫_ℂ •
ξ`. On the amplification by a nonunital C-star algebra `A`, coefficient and Hilbert actions
satisfy `L_(u*star v) D_(θ_(ξ,η)) = θ_(ξ⊗u,η⊗v)`.

Thus these products lie in the module compact ideal. Their compact-algebra values retain the
same endomorphism action, while pure vectors satisfy `(c • ξ)⊗a = c • (ξ⊗a)` and `ξ⊗(u*v) =
(ξ⊗u) <• v`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions InnerProductSpace
open CStarModule.InternalTensorProduct

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA

variable (H : Type uH)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Compact Hilbert-space rank-one operator.** For a complex Hilbert space `H` and `ξ,η : H`,
this element of `K(H)` acts by `ζ ↦ inner ℂ η ζ • ξ`. -/
def hilbertCompactRankOne (ξ η : H) :
    (compactEndomorphismClosedStarIdeal (H := H)).carrier := by
  refine ⟨InnerProductSpace.rankOne ℂ ξ η, ?_⟩
  change IsCompactOperator (InnerProductSpace.rankOne ℂ ξ η)
  have hcompact :=
    (isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℂ ξ)).comp_clm (_root_.innerSL ℂ (E := H) η)
  simpa only [InnerProductSpace.rankOne_def', ContinuousLinearMap.coe_comp] using hcompact

/-- **Action of a compact rank-one operator.** `(hilbertCompactRankOne H ξ η) ζ = inner ℂ η ζ •
ξ`. -/
theorem hilbertCompactRankOne_apply (ξ η ζ : H) :
    (hilbertCompactRankOne H ξ η : H →L[ℂ] H) ζ = inner ℂ η ζ • ξ :=
  rfl

/-- **Rank-one operator under compact-ideal inclusion.** The bounded operator underlying
`hilbertCompactRankOne H x y` is `InnerProductSpace.rankOne ℂ x y`. -/
@[simp]
theorem hilbertCompactRankOne_coe (x y : H) :
    (hilbertCompactRankOne H x y : H →L[ℂ] H) = InnerProductSpace.rankOne ℂ x y := rfl

/-- **Product of compact rank-one operators.** `θ_(x,y) θ_(z,w) = inner ℂ y z • θ_(x,w)`. -/
theorem hilbertCompactRankOne_mul (x y z w : H) :
    hilbertCompactRankOne H x y * hilbertCompactRankOne H z w = inner ℂ y z • hilbertCompactRankOne H x w := by
  apply Subtype.ext
  change (InnerProductSpace.rankOne ℂ x y).comp (InnerProductSpace.rankOne ℂ z w) =
    inner ℂ y z • InnerProductSpace.rankOne ℂ x w
  exact InnerProductSpace.rankOne_comp_rankOne x y z w

/-- **Adjoint of a compact rank-one operator.** `star (hilbertCompactRankOne H x y) =
hilbertCompactRankOne H y x`. -/
@[simp]
theorem hilbertCompactRankOne_star (x y : H) : star (hilbertCompactRankOne H x y) = hilbertCompactRankOne H y x := by
  apply Subtype.ext
  change star (InnerProductSpace.rankOne ℂ x y) = InnerProductSpace.rankOne ℂ y x
  simp only [ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]

variable (A : Type uA) [NonUnitalCStarAlgebra A]

/-- **Complex linearity of the Hilbert tensor factor.** `pure H A (c • ξ) b = c • pure H A ξ b`
for `c : ℂ`. -/
theorem pure_smul_left (c : ℂ) (ξ : H) (b : A) :
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    pure H A (c • ξ) b = c • pure H A ξ b := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  let : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  let : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  let : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  change completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm (c • ξ)) b =
    c • completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm ξ) b
  rw [map_smul]
  exact completedPure_smul_left (scalarSelfHom A) c ((ScalarRight.equivL H).symm ξ) b

/-- **Right action on a pure tensor.** For `ξ : H` and `u,v : A`, `pure H A ξ (u*v) = pure H A ξ u
<• v`. -/
theorem pure_right_smul (ξ : H) (u v : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    pure H A ξ (u * v) = pure H A ξ u <• v := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  let : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  let : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  let : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  change completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm ξ) (u * v) =
    completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm ξ) u <• v
  simpa only [CStarModule.Right.right_smul_self] using
    completedPure_right_smul (scalarSelfHom A) ((ScalarRight.equivL H).symm ξ) u v

/-- **Factorization of a module rank-one operator.** On `Space H A`, `coefficientHom (u*star v) *
hilbertOperator (rankOne ℂ ξ η)` equals the module rank-one operator defined by `pure ξ u` and
`pure η v`. -/
theorem coefficient_hilbertRankOne_eq_rankOne (ξ η : H) (u v : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    coefficientHom H A (u * star v) *
        hilbertOperator H A (InnerProductSpace.rankOne ℂ ξ η) =
      AdjointableOperator.rankOne (B := A) (pure H A ξ u) (pure H A η v) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  let : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  let : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  let : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  apply operator_ext_pure H A
  intro ζ b
  rw [AdjointableOperator.mul_apply, hilbertOperator_pure, coefficientHom_pure,
    AdjointableOperator.rankOne_apply, rightInner_pure]
  change pure H A (inner ℂ η ζ • ξ) ((u * star v) * b) =
    pure H A ξ u <• (inner ℂ η ζ • (star v * b))
  rw [pure_smul_left, CStarModule.right_smul_smul, ← pure_right_smul, mul_assoc]

/-- **Compactness of an elementary rank-one product.** The amplification operator `L_(u*star v)
D_(rankOne ℂ ξ η)` belongs to the module compact ideal, since it equals `θ_(ξ⊗u,η⊗v)`. -/
theorem coefficient_hilbertRankOne_mem_compact (ξ η : H) (u v : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    coefficientHom H A (u * star v) * hilbertOperator H A (InnerProductSpace.rankOne ℂ ξ η) ∈
      AdjointableOperator.compactSubmodule (B := A) (E := Space H A) (F := Space H A) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  let : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  let : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  let : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  rw [coefficient_hilbertRankOne_eq_rankOne]
  exact AdjointableOperator.rankOne_mem_compact (pure H A ξ u) (pure H A η v)

/-- **Elementary rank-one value in the compact algebra.** The element of `CompactAlgebra H A`
represented by `L_(u*star v) D_(rankOne ℂ ξ η)` is the module rank-one map `θ_(ξ⊗u,η⊗v)`. -/
def elementaryCompactRankOne (ξ η : H) (u v : A) : CompactAlgebra H A := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  let : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  let : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  let : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact ⟨AdjointableOperator.rankOne (B := A) (pure H A ξ u) (pure H A η v),
    AdjointableOperator.rankOne_mem_compact (pure H A ξ u) (pure H A η v)⟩

/-- **Endomorphism of the elementary compact.** The inclusion of `elementaryCompactRankOne H A ξ η
u v` into adjointable endomorphisms is `coefficientHom (u*star v) * hilbertOperator (rankOne ℂ
ξ η)`. -/
theorem elementaryCompactRankOne_coe (ξ η : H) (u v : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    (elementaryCompactRankOne H A ξ η u v : AdjointableOperator.End A (Space H A)) =
      coefficientHom H A (u * star v) * hilbertOperator H A (InnerProductSpace.rankOne ℂ ξ η) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  let : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  let : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  let : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact (coefficient_hilbertRankOne_eq_rankOne H A ξ η u v).symm

end

end CStarModule.HilbertAmplification
