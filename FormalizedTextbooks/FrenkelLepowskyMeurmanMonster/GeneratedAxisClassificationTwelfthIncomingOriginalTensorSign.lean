/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootNineTensorFactors
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityKleinFour

/-! The genuine compact incoming tensor retains all original source factors up to central sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Full original Q conjugation constrains the entire actual incoming tensor to two signs.
No equality of the compact spin scalar with the original word is assumed. -/
theorem generatedTwelfth_incoming_original_tensor_sign :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis)).2.2 =
        (∑ r : Fin 8, generatedFifthRootNineTensorFactor r 7) ∨
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedTwelfthIncomingCertifiedFiber)
      generatedFifthAxis)).2.2 =
        -(∑ r : Fin 8, generatedFifthRootNineTensorFactor r 7) := by
  have he : spinConjugation generatedTwelfthIncomingCertifiedFiber.val.1 =
      spinConjugation (generatedTenthQWordFiber 9).val.1 :=
    generatedTwelfth_incoming_spin_compact_oriented_conjugation
  rcases generatedTwelfth_full_Q_fiber_central_difference
      generatedTwelfthIncomingCertifiedFiber (generatedTenthQWordFiber 9) he with h | h
  · left
    rw [h, generatedTenth_Q_word_fiber_local,
      generatedAxisGlobalFifthRoot09Packet_actual, generatedFifthRootNine_incoming_tensor_factors]
  · right
    rw [h, map_mul, LinearEquiv.mul_apply]
    change (griessConwayEncode (localCentralGriess
      (rhoLocal (localFiberIntoH (generatedTenthQWordFiber 9)) generatedFifthAxis))).2.2 = _
    rw [localCentralGriess_encode, generatedTenth_Q_word_fiber_local,
      generatedAxisGlobalFifthRoot09Packet_actual, generatedFifthRootNine_incoming_tensor_factors]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
