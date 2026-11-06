/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneSpinBitPhase

/-! Compact signs retaining the original cocode Gaussian and genuine Pauli correction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Literal negative signs of the original diagonal Gaussian at all 4096 spin labels. -/
def generatedSeventhXiPlaneBitGammaRows : Fin 64 → ℕ :=
  ![
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117,
    0x8117811781178117
  ]

/-- The compact diagonal is still the original Fourier-normalized cocode Gaussian. -/
def generatedSeventhXiPlaneBitGamma (d : Fin 4096) : ℤ :=
  if (generatedSeventhXiPlaneBitGammaRows ⟨d.val / 64, by omega⟩).testBit (d.val % 64)
    then -1 else 1

/-- The literal central-one correction phase uses its actual modulation label 1613. -/
def generatedSeventhXiPlaneBitCorrectionPhase (d : Fin 4096) : ℤ :=
  if monsterNortonBitParity (d.val &&& 1613) then 1 else -1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
