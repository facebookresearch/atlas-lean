/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorExecutable

/-! Bounded certificates compare a weight-sign cache with the original physical Golay masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Displayed parity bits for checking against one fourth of each genuine original code weight. -/
def generatedSixthTensorWeightParityMask : ℕ :=
  (
    (0x9696c33c96969966a55ac33c6996699669960000 <<< 0) +
    (0xf0f0ff00ccccaaaaa55a96969966c33c9966a55a <<< 160) +
    (0xffff55aa33ccffffffff5a5affffffff0ff06666 <<< 320) +
    (0x3c3cffffffff55aaff00ccccf0f0aaaaffff3c3c <<< 480) +
    (0xff00aaaaffffffff33cc5a5affff0ff0ffff6666 <<< 640) +
    (0xffffffff3c3c55aaffff33ccffff5a5accccf0f0 <<< 800) +
    (0xdbb2bdd4177e177e177e7ee80ff0ffffffff6666 <<< 960) +
    (0xdbb2e87ee78ebdd4e78edbb2e87ebdd4e87ee78e <<< 1120) +
    (0x7ee8db4d7ee87ee88ee7e77171e77e174ddb2bbd <<< 1280) +
    (0x7e174ddb71e72bbd7ee8bd2b7ee8d4bdb2db7ee8 <<< 1440) +
    (0xb2dbdb4d7ee88ee77ee8e771bd2b7ee87ee8d4bd <<< 1600) +
    (0x7ee8b2db7ee8db4d4ddb71e77e172bbd7ee87ee8 <<< 1760) +
    (0x8ee77ee87ee8e7717ee87ee8bd2bd4bd <<< 1920)
  )

/-- The cached binary weight sign, used only after its actual weight certificates. -/
def generatedSixthTensorWeightParity (d : Fin 2048) : ZMod 2 :=
  if generatedSixthTensorWeightParityMask.testBit d.val then 1 else 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
