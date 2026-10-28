/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonQCacheData

/-! Exact complete binary and original central-cochain metadata of the three comparison caches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The binary coordinate image is precisely the stated original 24-bit word. -/
theorem generatedAxisGlobalOddComparisonQCache_base (k : Fin 3) (i : Fin 24) :
    toAdd (generatedAxisGlobalOddComparisonQCache k i).base =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddComparisonQCacheBinary k i) := rfl

set_option maxHeartbeats 2000000 in
-- Check every one of the 72 source central coefficients.
/-- Each packed bit is exactly the corresponding original central coefficient. -/
theorem generatedAxisGlobalOddComparisonMaskCoefficients_checked (k : Fin 3) (i : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddComparisonMaskCoefficients k) i =
      generatedAxisGlobalOddComparisonQCachePhase k i := by
  revert k i
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
-- Check all 1728 original triangular cocycle-difference entries.
/-- Every row bit equals the original cocycle difference of the complete binary images. -/
theorem generatedAxisGlobalOddComparisonMaskRows_checked (k : Fin 3) (i j : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddComparisonMaskRows k i) j =
      if i < j then
        qBeta
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddComparisonQCacheBinary k i))
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddComparisonQCacheBinary k j)) +
          qBeta (Pi.single i 1) (Pi.single j 1)
      else 0 := by
  revert k i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
