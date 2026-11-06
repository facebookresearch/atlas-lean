/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQCacheData

/-! Exact complete binary and original central-cochain metadata of the three comparison caches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The binary coordinate image is precisely the stated original 24-bit word. -/
theorem generatedAxisGlobalOddFourthQCache_base (k : Fin 4) (i : Fin 24) :
    toAdd (generatedAxisGlobalOddFourthQCache k i).base =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthQCacheBinary k i) := rfl

set_option maxHeartbeats 2000000 in
-- Check every one of the 96 source central coefficients.
/-- Each packed bit is exactly the corresponding original central coefficient. -/
theorem generatedAxisGlobalOddFourthMaskCoefficients_checked (k : Fin 4) (i : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthMaskCoefficients k) i =
      generatedAxisGlobalOddFourthQCachePhase k i := by
  revert k i
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
-- Check all 1968 original triangular cocycle-difference entries.
/-- Every row bit equals the original cocycle difference of the complete binary images. -/
theorem generatedAxisGlobalOddFourthMaskRows_checked (k : Fin 4) (i j : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthMaskRows k i) j =
      if i < j then
        qBeta
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthQCacheBinary k i))
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthQCacheBinary k j)) +
          qBeta (Pi.single i 1) (Pi.single j 1)
      else 0 := by
  revert k i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
