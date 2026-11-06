/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveAxis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedMatrixFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

/-! The complete actual positive canonical matrix is the genuine transported original matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem matrix_inclQ (q : Q) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (inclQ q) x)).1 = (griessConwayEncode x).1 := by
  change (griessConwayEncode (localGriessRepresentation (localFiberIncl q) x)).1 = _
  rw [localGriessRepresentation_encode]
  change conwayMatrixAction (1 : leechIsomSubgroup) (griessConwayEncode x).1 = _
  rw [map_one]
  rfl

/-- The actual final positive incoming axis has the complete original root-eight matrix. -/
theorem generatedRootEight_incoming_positive_triality_matrix :
    (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).1 =
      (griessConwayEncode generatedFifthRootEightAxis).1 := by
  obtain ⟨u, hp, hu⟩ := generatedRootEight_incoming_positive_projection_orbit
  have hr : u ∈ inclQ.range := by
    rw [inclQ_range_eq_projH_ker]
    exact hp
  obtain ⟨q, hq⟩ := hr
  rw [hu, ← hq, matrix_inclQ]

/-- Every coordinate of the actual canonical positive matrix is the genuine transported matrix. -/
theorem generatedRootEight_canonical_positive_matrix_actual :
    (griessConwayEncode generatedRootEightCanonicalPositiveAxis).1 =
      generatedRootEightMathieuCanonicalMatrix := by
  change (griessConwayEncode (localGriessRepresentation generatedRootEightCanonicalPositiveFiber
    generatedRootEightIncomingPositiveTrialityDestination)).1 = _
  rw [localGriessRepresentation_encode]
  change conwayMatrixAction generatedFifthRootEightCanonicalTransport
    (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).1 = _
  rw [generatedRootEight_incoming_positive_triality_matrix]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
