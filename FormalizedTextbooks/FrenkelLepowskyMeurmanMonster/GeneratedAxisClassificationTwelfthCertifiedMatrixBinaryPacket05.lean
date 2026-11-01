/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactBinaryCertificates

/-! Every binary column of complete certified spatial matrix 5. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check all original hyperbolic binary coordinates of this whole physical matrix.
/-- The integral lattice action retains exactly the original source binary columns. -/
theorem generatedTwelfth_certified_matrix_binary_packet_05 : ∀ j : Fin 24,
    (leechHyperbolicInverse *
      (generatedTwelfthCertifiedIntegral 5).map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
      monsterCo1GeometryBinaryMaskDecode (generatedTwelfthSpinCompactBinaryColumns 5 j) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
