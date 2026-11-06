/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSignFactors

/-! Complete original source sign phases, including the actual all-one contribution. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The three genuine original source signs, including both high-bit signs. -/
def generatedTwelfthTensorSourceSignCode : Fin 3 → Fin 4096 := ![768, 3072, 2048]

/-- The entire Y and Z phase data on all 2048 original low dictionary labels. -/
def generatedTwelfthTensorSourceSignPhaseData : Fin 3 → Fin 2 → Fin 32 → ℕ :=
  ![![![0xff033cc3c3c0000, 0xc3c30000f00f33cc, 0xcc33f00f00003c3c, 0xc3c3cc330ff0,
    0xa55a99669696aaaa, 0x6969aaaa5aa59966, 0x66995aa5aaaa9696, 0xaaaa69696699a55a,
    0xa55a99669696aaaa, 0x6969aaaa5aa59966, 0x66995aa5aaaa9696, 0xaaaa69696699a55a,
    0xff033cc3c3c0000, 0xc3c30000f00f33cc, 0xcc33f00f00003c3c, 0xc3c3cc330ff0,
    0xff033cc3c3c0000, 0xc3c30000f00f33cc, 0xcc33f00f00003c3c, 0xc3c3cc330ff0,
    0x5aa5669969695555, 0x96965555a55a6699, 0x9966a55a55556969, 0x5555969699665aa5,
    0x5aa5669969695555, 0x96965555a55a6699, 0x9966a55a55556969, 0x5555969699665aa5,
    0xff033cc3c3c0000, 0xc3c30000f00f33cc, 0xcc33f00f00003c3c, 0xc3c3cc330ff0],
    ![0xa55a99669696aaaa, 0x6969aaaa5aa59966, 0x66995aa5aaaa9696, 0xaaaa69696699a55a,
    0xff033cc3c3c0000, 0xc3c30000f00f33cc, 0xcc33f00f00003c3c, 0xc3c3cc330ff0,
    0xff033cc3c3c0000, 0xc3c30000f00f33cc, 0xcc33f00f00003c3c, 0xc3c3cc330ff0,
    0xa55a99669696aaaa, 0x6969aaaa5aa59966, 0x66995aa5aaaa9696, 0xaaaa69696699a55a,
    0x5aa5669969695555, 0x96965555a55a6699, 0x9966a55a55556969, 0x5555969699665aa5,
    0xff033cc3c3c0000, 0xc3c30000f00f33cc, 0xcc33f00f00003c3c, 0xc3c3cc330ff0,
    0xff033cc3c3c0000, 0xc3c30000f00f33cc, 0xcc33f00f00003c3c, 0xc3c3cc330ff0,
    0x5aa5669969695555, 0x96965555a55a6699, 0x9966a55a55556969, 0x5555969699665aa5]],
    ![![0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8],
    ![0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
    0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117]],
    ![![0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff], ![0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]]]

/-- Every genuine source Y or Z phase sign, without omitted dictionary coordinates. -/
def generatedTwelfthTensorSourceSignPhase (j : Fin 3) (p : Fin 2) (e : Fin 2048) : ℤ :=
  if (generatedTwelfthTensorSourceSignPhaseData j p
    ⟨e.val / 64, by omega⟩).testBit (e.val % 64) then -1 else 1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
