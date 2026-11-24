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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.ElementaryCompacts
public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.HilbertHom
public import MathlibExt.Analysis.InnerProductSpace.CompactOperator.FiniteRankClosure

import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-!
# The actual arbitrary coefficient and full-H compact product image

The original elementary rank-one identity gives compact image for coefficient
products a * star e. The genuine approximate unit converges to each original
coefficient, and the same coefficient representation is continuous. Then the
actual norm closure of full-H Hilbert rank-one spans and continuity of the
original factor action give compact image for every actual compact T.

The resulting value is in the existing CompactAlgebra H A. No compactness,
output model or norm identity is supplied as a premise. This is a constructor
prerequisite for the actual algebraic A tensor K(full H) map in Blackadar10.1.2;
its minimum completion and the terminal Takai theorem are separate obligations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions Topology
open Filter CStarModule.InternalTensorProduct

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA

variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]

/-- The original Hilbert rank-one factor has compact module image for every original coefficient. -/
theorem coefficient_hilbertRankOne_mem_compact_allCoefficients (a : A) (ξ η : H) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    coefficientHom H A a * hilbertOperator H A (InnerProductSpace.rankOne ℂ ξ η) ∈
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
  let : CompleteSpace (Space H A) := by
    exact inferInstanceAs
      (CompleteSpace (CompletedTensor (E₁ := ScalarRight H) (scalarSelfHom A)))
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hmul : Tendsto (fun e : A => a * e) (CStarAlgebra.approximateUnit A) (nhds a) :=
    (CStarAlgebra.increasingApproximateUnit (A := A)).tendsto_mul_left a
  have hcoef : Tendsto (fun e : A => a * star e) (CStarAlgebra.approximateUnit A) (nhds a) := by
    apply hmul.congr'
    filter_upwards [(CStarAlgebra.increasingApproximateUnit (A := A)).eventually_star_eq] with e he
    rw [he]
  have hOperators : Tendsto
      (fun e : A => coefficientHom H A (a * star e) *
        hilbertOperator H A (InnerProductSpace.rankOne ℂ ξ η))
      (CStarAlgebra.approximateUnit A)
      (nhds (coefficientHom H A a * hilbertOperator H A (InnerProductSpace.rankOne ℂ ξ η))) :=
    (((map_continuous (coefficientHom H A)).tendsto a).comp hcoef).mul tendsto_const_nhds
  have hmem : coefficientHom H A a * hilbertOperator H A (InnerProductSpace.rankOne ℂ ξ η) ∈
      closure (AdjointableOperator.compactSubmodule
        (B := A) (E := Space H A) (F := Space H A) :
          Set (AdjointableOperator.End A (Space H A))) :=
    mem_closure_of_tendsto hOperators (Eventually.of_forall fun e =>
      coefficient_hilbertRankOne_mem_compact H A ξ η a e)
  rw [(AdjointableOperator.isClosed_compactSubmodule
    (B := A) (E := Space H A) (F := Space H A)).closure_eq] at hmem
  exact hmem

/-- Every original compact Hilbert operator has actual compact module image with every coefficient. -/
theorem coefficient_hilbertOperator_mem_compact (a : A) (T : H →L[ℂ] H)
    (hT : IsCompactOperator T) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    coefficientHom H A a * hilbertOperator H A T ∈
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
  let : CompleteSpace (Space H A) := by
    exact inferInstanceAs
      (CompleteSpace (CompletedTensor (E₁ := ScalarRight H) (scalarSelfHom A)))
  let K : Submodule ℂ (AdjointableOperator.End A (Space H A)) :=
    AdjointableOperator.compactSubmodule (B := A) (E := Space H A) (F := Space H A)
  let F : (H →L[ℂ] H) →ₗ[ℂ] AdjointableOperator.End A (Space H A) :=
    { toFun := fun U => coefficientHom H A a * hilbertHom H A U
      map_add' := fun U V => by rw [map_add, mul_add]
      map_smul' := fun c U => by
        rw [map_smul]
        exact mul_smul_comm c (coefficientHom H A a) (hilbertHom H A U) }
  let S : Submodule ℂ (H →L[ℂ] H) := K.comap F
  have hF : Continuous F := by
    change Continuous (fun U : H →L[ℂ] H => coefficientHom H A a * hilbertHom H A U)
    exact continuous_const.mul (map_continuous (hilbertHom H A))
  have hSclosed : IsClosed (S : Set (H →L[ℂ] H)) := by
    change IsClosed (F ⁻¹' (K : Set (AdjointableOperator.End A (Space H A))))
    exact (AdjointableOperator.isClosed_compactSubmodule
      (B := A) (E := Space H A) (F := Space H A)).preimage hF
  have hspan : InnerProductSpace.finiteRankSubmodule (𝕜 := ℂ) (E := H) (F := H) ≤ S := by
    change Submodule.span ℂ
      (Set.range fun p : H × H => InnerProductSpace.rankOne ℂ p.1 p.2) ≤ S
    apply Submodule.span_le.2
    rintro _ ⟨⟨ξ, η⟩, rfl⟩
    change coefficientHom H A a * hilbertHom H A (InnerProductSpace.rankOne ℂ ξ η) ∈ K
    simpa only [hilbertHom_apply] using
      coefficient_hilbertRankOne_mem_compact_allCoefficients H A a ξ η
  have hTcl := hT.mem_topologicalClosure_finiteRankSubmodule (𝕜 := ℂ)
  change T ∈ closure (InnerProductSpace.finiteRankSubmodule
    (𝕜 := ℂ) (E := H) (F := H) : Set (H →L[ℂ] H)) at hTcl
  have hClosure : closure (InnerProductSpace.finiteRankSubmodule
      (𝕜 := ℂ) (E := H) (F := H) : Set (H →L[ℂ] H)) ⊆ S :=
    closure_minimal (fun U hU => hspan hU) hSclosed
  have hmem : T ∈ S := hClosure hTcl
  change coefficientHom H A a * hilbertHom H A T ∈ K at hmem
  simpa only [hilbertHom_apply] using hmem

/-- The two original algebraic tensor factors have actual compact module product image. -/
theorem coefficient_compactHilbertHom_mem_compact (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    coefficientHom H A a * compactHilbertHom H A T ∈
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
  have hT := T.property
  change IsCompactOperator (T : H →L[ℂ] H) at hT
  rw [compactHilbertHom_apply]
  exact coefficient_hilbertOperator_mem_compact H A a (T : H →L[ℂ] H) hT

/-- Compute the original arbitrary coefficient/compact product in the actual compact algebra. -/
def compactElementaryOperator (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) : CompactAlgebra H A := by
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
  exact ⟨coefficientHom H A a * compactHilbertHom H A T,
    coefficient_compactHilbertHom_mem_compact H A a T⟩

/-- The computed compact element keeps the literal original product of the two factors. -/
theorem compactElementaryOperator_coe (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    (compactElementaryOperator H A a T : AdjointableOperator.End A (Space H A)) =
      coefficientHom H A a * compactHilbertHom H A T := by
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
  rfl

end

end CStarModule.HilbertAmplification
