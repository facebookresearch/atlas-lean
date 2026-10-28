/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot11
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageFirstLayer

/-! The actual inverse twelfth-root transition has the genuine octad-image local destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Cancelling the outer triality gives an exact full-vector local octad-image word. -/
theorem generatedAxisGlobalFifthRoot11_negative_word :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis) =
      rhoLocal (localFiberIntoH generatedFifthLocalFiber)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)) := by
  rw [generatedAxisGlobalFifthRoot11_localWord, map_one]
  change sExtra.symm generatedFifthAxis = _
  rw [generatedFifthAxis_local_expression, sExtra.symm_apply_apply]

/-- The entire inverse twelfth-root transition belongs to the already proved first local layer. -/
theorem generatedAxisGlobalFifthRoot11_negative_firstLayer :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalFirstLayer := by
  rw [generatedAxisGlobalFifthRoot11_negative_word]
  exact generatedLocalOrbitUnion_local generatedAxisGlobalFirstLayer
    (localFiberIntoH generatedFifthLocalFiber)
    (generatedAxisGlobalFirstLayer_contains_triality
      (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

/-- Its actual local class is the genuine octad-image class, by an exact full-vector word. -/
theorem generatedAxisGlobalFifthRoot11_negative_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace)
      (sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis)) =
      generatedAxisOctadDestination := by
  rw [generatedAxisGlobalFifthRoot11_negative_word]
  have he : Quotient.mk (MulAction.orbitRel H GriessSpace)
      (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))) =
      Quotient.mk (MulAction.orbitRel H GriessSpace)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)) := by
    apply (generatedAxis_local_class_eq_iff _ _).mpr
    refine ⟨(localFiberIntoH generatedFifthLocalFiber)⁻¹, ?_⟩
    rw [map_inv]
    exact (rhoLocal (localFiberIntoH generatedFifthLocalFiber)).symm_apply_apply _
  exact he.trans ((generatedAxis_triality_octad_class_iff _ _).mpr
    ⟨generatedFourthOctad, 0, rfl⟩)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
