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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.AlgebraicTensorHom

import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic

/-!
# Dense range of the actual algebraic compact tensor action

The original completed pure vectors have dense complex span. Rank-one module
operators are continuous linear in their first vector and continuous star
semilinear in their second. The actual elementary tensor range contains every
pure-pair rank-one, hence its closed span contains every original rank-one.
The genuine compact module ideal is exactly that norm-closed rank-one span.

Subtype inducing topology gives dense range of the actual algebraic tensor
homomorphism in the existing CompactAlgebra H A. This is the missing onto
comparison prerequisite for its actually induced completion, not a proof of
raw injectivity, the least cross norm or the terminal Takai theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions TensorProduct Topology
open CStarModule.InternalTensorProduct

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA

variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]

/-- The original Hilbert/coefficient pure vectors have dense complex span in the actual completion. -/
theorem pure_dense_span :
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    Dense (Submodule.span ℂ (Set.range fun p : H × A => pure H A p.1 p.2) : Set (Space H A)) := by
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
  have hRange : Set.range (fun p : H × A => pure H A p.1 p.2) =
      Set.range (fun p : ScalarRight H × A => completedPure (scalarSelfHom A) p.1 p.2) := by
    ext x
    constructor
    · rintro ⟨⟨ξ, a⟩, rfl⟩
      exact ⟨((ScalarRight.equivL H).symm ξ, a), rfl⟩
    · rintro ⟨⟨ξ, a⟩, rfl⟩
      refine ⟨(ScalarRight.equivL H ξ, a), ?_⟩
      change completedPure (scalarSelfHom A)
        ((ScalarRight.equivL H).symm (ScalarRight.equivL H ξ)) a =
          completedPure (scalarSelfHom A) ξ a
      rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hRange]
  exact completedPure_dense_span (E₁ := ScalarRight H) (scalarSelfHom A)

/-- The actual algebraic tensor operator range closes to the original compact module ideal. -/
theorem closure_range_algebraicTensorOperator_eq_compactSubmodule :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    (LinearMap.range (algebraicTensorOperator H A)).topologicalClosure =
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
  let E := Space H A
  let D := AdjointableOperator.End A E
  let R : Submodule ℂ D := (LinearMap.range (algebraicTensorOperator H A)).topologicalClosure
  have hRclosed : IsClosed (R : Set D) := (LinearMap.range (algebraicTensorOperator H A)).isClosed_topologicalClosure
  let left (y : E) : E →L[ℂ] D :=
    ({ toFun := fun x => AdjointableOperator.rankOne (B := A) x y
       map_add' := fun x x' => by
         apply AdjointableOperator.ext
         intro z
         change (x + x') <• rightInner (B := A) y z =
           x <• rightInner (B := A) y z + x' <• rightInner (B := A) y z
         exact CStarModule.add_right_smul x x' (rightInner (B := A) y z)
       map_smul' := fun c x => by
         apply AdjointableOperator.ext
         intro z
         change (c • x) <• rightInner (B := A) y z = c • (x <• rightInner (B := A) y z)
         exact CStarModule.smul_right_smul c x (rightInner (B := A) y z) } : E →ₗ[ℂ] D).mkContinuous ‖y‖
      (fun x => by
        change ‖AdjointableOperator.rankOne (B := A) x y‖ ≤ ‖y‖ * ‖x‖
        simpa only [mul_comm] using (AdjointableOperator.norm_rankOne_le (B := A) x y))
  let right (x : E) : E →L⋆[ℂ] D :=
    ({ toFun := fun y => AdjointableOperator.rankOne (B := A) x y
       map_add' := fun y y' => by
         apply AdjointableOperator.ext
         intro z
         change x <• rightInner (B := A) (y + y') z =
           x <• rightInner (B := A) y z + x <• rightInner (B := A) y' z
         rw [CStarModule.rightInner_add_left, CStarModule.right_smul_add]
       map_smul' := fun c y => by
         change AdjointableOperator.rankOne (B := A) x (c • y) =
           star c • AdjointableOperator.rankOne (B := A) x y
         apply AdjointableOperator.ext
         intro z
         simp only [AdjointableOperator.rankOne_apply, AdjointableOperator.smul_apply,
           CStarModule.rightInner_smul_left, CStarModule.right_smul_smul] } :
        E →ₗ⋆[ℂ] D).mkContinuous ‖x‖ (fun y => AdjointableOperator.norm_rankOne_le (B := A) x y)
  have hPure (ξ η : H) (u v : A) :
      AdjointableOperator.rankOne (B := A) (pure H A ξ u) (pure H A η v) ∈ R := by
    apply Submodule.le_topologicalClosure
    refine ⟨(u * star v) ⊗ₜ[ℂ] hilbertCompactRankOne H ξ η, ?_⟩
    rw [algebraicTensorOperator_tmul, compactElementaryOperator_coe, compactHilbertHom_apply]
    change coefficientHom H A (u * star v) * hilbertOperator H A (InnerProductSpace.rankOne ℂ ξ η) =
      AdjointableOperator.rankOne (B := A) (pure H A ξ u) (pure H A η v)
    exact coefficient_hilbertRankOne_eq_rankOne H A ξ η u v
  have hdense : Dense (Submodule.span ℂ (Set.range fun p : H × A => pure H A p.1 p.2) : Set E) :=
    pure_dense_span H A
  have hLeft (η : H) (v : A) (x : E) :
      AdjointableOperator.rankOne (B := A) x (pure H A η v) ∈ R := by
    let P : Submodule ℂ E := R.comap (left (pure H A η v)).toLinearMap
    have hPclosed : IsClosed (P : Set E) := by
      change IsClosed ((left (pure H A η v)) ⁻¹' (R : Set D))
      exact hRclosed.preimage (left (pure H A η v)).continuous
    have hspan : Submodule.span ℂ (Set.range fun p : H × A => pure H A p.1 p.2) ≤ P := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨ξ, u⟩, rfl⟩
      change AdjointableOperator.rankOne (B := A) (pure H A ξ u) (pure H A η v) ∈ R
      exact hPure ξ η u v
    have hx : x ∈ P := (closure_minimal (fun _ h => hspan h) hPclosed) (hdense x)
    exact hx
  have hAll (x y : E) : AdjointableOperator.rankOne (B := A) x y ∈ R := by
    let P : Submodule ℂ E := R.comap (right x).toLinearMap
    have hPclosed : IsClosed (P : Set E) := by
      change IsClosed ((right x) ⁻¹' (R : Set D))
      exact hRclosed.preimage (right x).continuous
    have hspan : Submodule.span ℂ (Set.range fun p : H × A => pure H A p.1 p.2) ≤ P := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨η, v⟩, rfl⟩
      change AdjointableOperator.rankOne (B := A) x (pure H A η v) ∈ R
      exact hLeft η v x
    have hy : y ∈ P := (closure_minimal (fun _ h => hspan h) hPclosed) (hdense y)
    exact hy
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ ?_ AdjointableOperator.isClosed_compactSubmodule
    rintro _ ⟨z, rfl⟩
    exact algebraicTensorOperator_mem_compact H A z
  · change (AdjointableOperator.finiteRankSubmodule (B := A) (E := E) (F := E)).topologicalClosure ≤ R
    apply Submodule.topologicalClosure_minimal _ ?_ hRclosed
    apply Submodule.span_le.2
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact hAll x y

/-- The actual algebraic A tensor K(full H) hom has dense range in the original compact module algebra. -/
theorem denseRange_algebraicCompactTensorHom :
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    DenseRange (algebraicCompactTensorHom H A) := by
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
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  let ι : CompactAlgebra H A → AdjointableOperator.End A (Space H A) := Subtype.val
  have hι : Topology.IsInducing ι := Topology.IsInducing.subtypeVal
  change Dense (Set.range (algebraicCompactTensorHom H A))
  apply hι.dense_iff.mpr
  intro T
  have hImage : ι '' Set.range (algebraicCompactTensorHom H A) =
      Set.range (algebraicTensorOperator H A) := by
    ext U
    constructor
    · rintro ⟨S, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨algebraicCompactTensorHom H A z, ⟨z, rfl⟩, rfl⟩
  rw [hImage]
  change (T : AdjointableOperator.End A (Space H A)) ∈
    (LinearMap.range (algebraicTensorOperator H A)).topologicalClosure
  rw [closure_range_algebraicTensorOperator_eq_compactSubmodule]
  exact T.property

end

end CStarModule.HilbertAmplification
