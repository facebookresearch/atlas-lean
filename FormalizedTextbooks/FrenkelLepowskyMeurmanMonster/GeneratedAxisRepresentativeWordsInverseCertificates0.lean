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
/-- The full inverse phase for compact node 0 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate0 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (0 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (0 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (0 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (0 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (0 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (0 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (0 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 1 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate1 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (1 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (1 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (1 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (1 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (1 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (1 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (1 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 2 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate2 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (2 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (2 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (2 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (2 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (2 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (2 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (2 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 3 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate3 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (3 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (3 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (3 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (3 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (3 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (3 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (3 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel


set_option maxHeartbeats 80000000 in
-- A bounded explicit twelve-coordinate phase/edge calculation is kernel checked.
/-- The full inverse phase for compact node 4 is kernel checked. -/
theorem representativeNodeSpin_inverse_phase_certificate4 :
    (∀ i : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (4 : Fin 15)))
        (Pi.single i 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (4 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (4 : Fin 15))).col i)) ∧
    (∀ i j : Fin 12,
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodeInversePhaseRows (4 : Fin 15)))
        (Pi.single i 1 + Pi.single j 1) =
      monsterMonomialQuadratic
      (representativeMatrix (representativeNodePhaseRows (4 : Fin 15)))
        ((representativeMatrix (representativeNodeInverseRows (4 : Fin 15))).col i +
          (representativeMatrix (representativeNodeInverseRows (4 : Fin 15))).col j)) := by
  simp only [representativeQuadratic_single, representativeQuadratic_single_add]
  decide +kernel



end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
