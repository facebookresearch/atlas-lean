/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFrameAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorFactors

/-! Exact original positive incoming physical columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The integer numerator of all eight genuine incoming physical columns. -/
def generatedRootEightIncomingSpatialNumerator : Fin 8 → Fin 24 → ℤ :=
  ![![0, 2, -2, 0, 1, 1, -1, -1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, -1, 1, -1, 0, 0, 0, 0, -2, 0, 2, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, 1, -1, 1, -1, 0, 0, 0, 0, 1, -1, 1, -1, -1, -1, -1, -1],
    ![1, 1, 1, 1, 0, 0, 0, 0, -1, 1, -1, 1, 0, 0, 0, 0, -1, 1, -1, 1, -1, -1, -1, -1],
    ![0, 0, 0, 0, -1, 1, -1, 1, -2, 0, 0, -2, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 0, 0, 0, 0, -1, 1, -1, 1, 0, 0, 0, 0, 1, -1, 1, -1, 1, 1, 1, 1],
    ![0, 0, 0, 0, -1, 1, 1, -1, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, -2, -2, 0, 0, 0, 0],
    ![1, -1, -1, 1, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0, 0, -1, 1, 1, -1, -1, 1, -1, 1]]

set_option maxHeartbeats 4000000 in
/-- The complete original checked spatial frame agrees with every numerator coordinate. -/
theorem generatedRootEight_incoming_spatial_frame_certificate : ∀ r : Fin 8, ∀ i : Fin 24,
    generatedFifthRootEightFrameData 7 (generatedTwelfthTensorSourceCoordinate r) i =
      2 * generatedRootEightIncomingSpatialNumerator r i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
