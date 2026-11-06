/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitMaskData

/-! Exact decoding of the original binary matrices and their central cochains. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

set_option maxHeartbeats 0 in
-- Ordinary kernel evaluation checks all entries of the finite original matrices.
/-- Every column mask is the corresponding column of the original binary operator. -/
theorem co1NonsplitColumnMasks_decode (k : Fin 5) :
    ∀ i j : Fin 24, monsterCo1GeometryBinaryMaskDecode
      (co1NonsplitColumnMasks k j) i = omegaOrbitBinaryMatrices k i j := by
  fin_cases k <;> decide +kernel

set_option maxHeartbeats 0 in
-- Ordinary kernel evaluation checks all entries of the finite original matrices.
/-- The stored phase matrix is exactly the upper-triangular cocycle difference. -/
theorem co1NonsplitPhaseMasks_decode (k : Fin 5) :
    ∀ i j : Fin 24, monsterCo1GeometryBinaryMaskDecode (co1NonsplitPhaseMasks k i) j =
      if i < j then
        qBeta (monsterCo1GeometryBinaryMaskDecode (co1NonsplitColumnMasks k i))
          (monsterCo1GeometryBinaryMaskDecode (co1NonsplitColumnMasks k j)) +
            qBeta (Pi.single i 1) (Pi.single j 1)
      else 0 := by
  fin_cases k <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
