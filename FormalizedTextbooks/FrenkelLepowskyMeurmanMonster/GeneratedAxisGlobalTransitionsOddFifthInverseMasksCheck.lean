/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthInverseMasksData

/-! Finite full binary and central certificates for original Fourth inverse-frame masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Every inverse binary column returns the actual full original forward coordinate unit. -/
theorem generatedAxisGlobalOddFifthInverseMaskColumn_checked (k : Fin 2) (i : Fin 24) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFifthQCacheBinary k)
      (generatedAxisGlobalOddFifthInverseMaskColumns k i) = 2 ^ i.val := by
  revert k i
  decide +kernel

/-- Every inverse central bit returns the original positive central section of its coordinate unit. -/
theorem generatedAxisGlobalOddFifthInverseMaskPhase_checked (k : Fin 2) (i : Fin 24) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFifthMaskRows k)
        (generatedAxisGlobalOddFifthMaskCoefficients k)
        (generatedAxisGlobalOddFifthInverseMaskColumns k i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalOddFifthInverseMaskPhases k i := by
  revert k i
  decide +kernel

/-- Every inverse correction row is the complete original cocycle difference of its binary columns. -/
theorem generatedAxisGlobalOddFifthInverseMaskRows_checked (k : Fin 2) (i j : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskRows k i) j =
      if i < j then
        qBeta (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskColumns k i))
          (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskColumns k j)) +
        qBeta (Pi.single i 1) (Pi.single j 1)
      else 0 := by
  revert k i j
  decide +kernel

/-- Every inverse packed correction bit retains the original full inverse central phase. -/
theorem generatedAxisGlobalOddFifthInverseMaskCoefficients_checked (k : Fin 2) (i : Fin 24) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthInverseMaskCoefficients k) i =
      generatedAxisGlobalOddFifthInverseMaskPhases k i := by
  revert k i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
