/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMasksData

/-! Exact complete binary and original central-cochain metadata of the three comparison caches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The binary coordinate image is precisely the stated original 24-bit word. -/
theorem generatedAxisGlobalOddFifthQCache_base (k : Fin 2) (i : Fin 24) :
    toAdd (generatedAxisGlobalOddFifthQCache k i).base =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthQCacheBinary k i) := rfl

set_option maxHeartbeats 2000000 in
-- Check every one of the 48 source central coefficients.
/-- Each packed bit is exactly the corresponding original central coefficient. -/
theorem generatedAxisGlobalOddFifthMaskCoefficients_checked (k : Fin 2) (i : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthMaskCoefficients k) i =
      generatedAxisGlobalOddFifthQCachePhase k i := by
  revert k i
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
-- Check all 1152 original triangular cocycle-difference entries.
/-- Every row bit equals the original cocycle difference of the complete binary images. -/
theorem generatedAxisGlobalOddFifthMaskRows_checked (k : Fin 2) (i j : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthMaskRows k i) j =
      if i < j then
        qBeta
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthQCacheBinary k i))
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthQCacheBinary k j)) +
          qBeta (Pi.single i 1) (Pi.single j 1)
      else 0 := by
  revert k i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
