/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinCircuit

/-! Compact data for the actual diagonal Gaussian signs, including the global minus. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Positive sign masks in consecutive blocks of 64 original spin coordinates. -/
def generatedSixthSpinGammaPositive : Fin 64 → ℕ :=
![
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
  0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8]

/-- Executable diagonal Gaussian sign; its original-source certification is separate. -/
def generatedSixthSpinGammaFast (n : Fin 4096) : ℤ :=
  if (generatedSixthSpinGammaPositive ⟨n.val / 64, by omega⟩).testBit (n.val % 64)
    then 1 else -1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
