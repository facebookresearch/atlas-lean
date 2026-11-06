/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMasksData

/-! Exact full coordinate and cocycle metadata for the fourteen source-derived Q-image tables. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The candidate image table has the precise original decoded binary coordinates. -/
theorem generatedAxisGlobalFifthQCache_base (k : Fin 14) (i : Fin 24) :
    toAdd (generatedAxisGlobalFifthQCache k i).base =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthQCacheBinary k i) := by
  funext j
  cases h : (generatedAxisGlobalFifthQCacheBinary k i).testBit j.val <;>
    simp [generatedAxisGlobalFifthQCache, monsterCo1GeometryBinaryMaskDecode,
      golayBooleanCast, h]

set_option maxHeartbeats 20000000 in
-- Check all336 original central unit coefficients, without any group-action assumption.
/-- Every packed bit is exactly the original candidate central coefficient. -/
theorem generatedAxisGlobalFifthMaskCoefficients_checked (k : Fin 14) (i : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthMaskCoefficients k) i =
      generatedAxisGlobalFifthQCachePhase k i := by
  revert k i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check all8064 triangular cochain bits against the original actual Q cocycle formula.
set_option maxRecDepth 10000 in
/-- Every phase-matrix bit is the precise cocycle difference of the source-derived columns. -/
theorem generatedAxisGlobalFifthMaskRows_checked (k : Fin 14) (i j : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthMaskRows k i) j =
      if i < j then
        qBeta
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthQCacheBinary k i))
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthQCacheBinary k j)) +
          qBeta (Pi.single i 1) (Pi.single j 1)
      else 0 := by
  revert k i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
