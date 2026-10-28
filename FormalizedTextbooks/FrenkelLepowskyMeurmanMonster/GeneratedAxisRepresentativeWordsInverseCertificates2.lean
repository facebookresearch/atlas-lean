/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded kernel certificates of complete spin coordinate and sign actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsOriginalCertificates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 10 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate10 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (10 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (10 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (10 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (10 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (10 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (10 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (10 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 11 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate11 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (11 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (11 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (11 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (11 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (11 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (11 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (11 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 12 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate12 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (12 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (12 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (12 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (12 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (12 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (12 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (12 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 13 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate13 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (13 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (13 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (13 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (13 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (13 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (13 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (13 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 14 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate14 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (14 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (14 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (14 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (14 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (14 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (14 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (14 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
