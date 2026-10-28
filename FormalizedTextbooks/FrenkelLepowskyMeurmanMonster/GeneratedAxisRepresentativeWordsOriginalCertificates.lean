/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Bounded kernel checks of full representative spin signs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlanDecidable

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 8000000 in
-- These checks cover only the two frozen 12 by 12 source-generator coefficient arrays.
/-- The first two node matrices and phases are exactly the frozen actual source data. -/
theorem representativeNodeSpin_original_certificate : ∀ k : Fin 2,
    representativeMatrix (representativeNodeCoordinateRows (Fin.castAdd 13 k)) =
      monsterSourcePermutationCodeMatrix (Fin.castAdd 2 k) ∧
    representativeMatrix (representativeNodePhaseRows (Fin.castAdd 13 k)) =
      monsterSourcePermutationPhaseData k := by
  have h : ∀ k : Fin 2, ∀ i j : Fin 12,
      representativeMatrix (representativeNodeCoordinateRows (Fin.castAdd 13 k)) i j =
        monsterSourcePermutationCodeMatrix (Fin.castAdd 2 k) i j ∧
      representativeMatrix (representativeNodePhaseRows (Fin.castAdd 13 k)) i j =
        monsterSourcePermutationPhaseData k i j := by
    decide +kernel
  intro k
  constructor
  · funext i j
    exact (h k i j).1
  · funext i j
    exact (h k i j).2


set_option maxHeartbeats 8000000 in
-- Each node checks a 12 by 12 finite matrix product against its stored inverse.
/-- The explicit inverse matrix of every compact node really is an inverse. -/
theorem representativeNodeSpin_inverse_matrix_certificate : ∀ n : Fin 15,
    representativeMatrix (representativeNodeCoordinateRows n) *
      representativeMatrix (representativeNodeInverseRows n) = 1 := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
