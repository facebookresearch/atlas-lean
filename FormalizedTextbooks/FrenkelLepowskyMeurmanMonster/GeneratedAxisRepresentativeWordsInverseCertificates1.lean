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
/-- The full inverse phase for compact node 5 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate5 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (5 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (5 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (5 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (5 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (5 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (5 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (5 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 6 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate6 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (6 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (6 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (6 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (6 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (6 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (6 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (6 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 7 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate7 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (7 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (7 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (7 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (7 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (7 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (7 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (7 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 8 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate8 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (8 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (8 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (8 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (8 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (8 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (8 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (8 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 9 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate9 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (9 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (9 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (9 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (9 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (9 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (9 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (9 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
