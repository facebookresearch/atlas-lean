/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSignFactors

/-! Source sign phases for the three root-two sign codes not used by the Twelfth source. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The three root-two source sign codes `0`, `1024` and `2304`. -/
def generatedFeasibleAmbientTenthSignCode : Fin 3 → Fin 4096 := ![0, 1024, 2304]

/-- The Y and Z phase data on all 2048 low dictionary labels. -/
def generatedFeasibleAmbientTenthSignPhaseData : Fin 3 → Fin 2 → Fin 32 → ℕ :=
  ![![![0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0], ![0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]], ![![0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117], ![0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117]], ![![0xcc33c3c3f00fffff,
      0x3c3c33ccfffff00f, 0xffff0ff03c3ccc33, 0xff0ffff33ccc3c3, 0xcc33c3c3f00fffff,
      0x3c3c33ccfffff00f, 0xffff0ff03c3ccc33, 0xff0ffff33ccc3c3, 0x669969695aa55555,
      0x9696996655555aa5, 0x5555a55a96966699, 0xa55a555599666969, 0x669969695aa55555,
      0x9696996655555aa5, 0x5555a55a96966699, 0xa55a555599666969, 0xcc33c3c3f00fffff,
      0x3c3c33ccfffff00f, 0xffff0ff03c3ccc33, 0xff0ffff33ccc3c3, 0xcc33c3c3f00fffff,
      0x3c3c33ccfffff00f, 0xffff0ff03c3ccc33, 0xff0ffff33ccc3c3, 0x99669696a55aaaaa,
      0x69696699aaaaa55a, 0xaaaa5aa569699966, 0x5aa5aaaa66999696, 0x99669696a55aaaaa,
      0x69696699aaaaa55a, 0xaaaa5aa569699966, 0x5aa5aaaa66999696], ![0x99669696a55aaaaa,
      0x69696699aaaaa55a, 0xaaaa5aa569699966, 0x5aa5aaaa66999696, 0x99669696a55aaaaa,
      0x69696699aaaaa55a, 0xaaaa5aa569699966, 0x5aa5aaaa66999696, 0x33cc3c3c0ff00000,
      0xc3c3cc3300000ff0, 0xf00fc3c333cc, 0xf00f0000cc333c3c, 0x33cc3c3c0ff00000,
      0xc3c3cc3300000ff0, 0xf00fc3c333cc, 0xf00f0000cc333c3c, 0x669969695aa55555,
      0x9696996655555aa5, 0x5555a55a96966699, 0xa55a555599666969, 0x669969695aa55555,
      0x9696996655555aa5, 0x5555a55a96966699, 0xa55a555599666969, 0x33cc3c3c0ff00000,
      0xc3c3cc3300000ff0, 0xf00fc3c333cc, 0xf00f0000cc333c3c, 0x33cc3c3c0ff00000,
      0xc3c3cc3300000ff0, 0xf00fc3c333cc, 0xf00f0000cc333c3c]]]

/-- Every source Y or Z phase sign. -/
def generatedFeasibleAmbientTenthSignPhase (j : Fin 3) (p : Fin 2) (e : Fin 2048) : ℤ :=
  if (generatedFeasibleAmbientTenthSignPhaseData j p ⟨e.val / 64, by omega⟩).testBit (e.val % 64)
      then -1 else 1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
