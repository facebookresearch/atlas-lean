/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedEvaluation

/-! Complete signed preferred-Q packet returns for positions 19456 through 19967. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check both inverse indices, the full binary image and every original central phase.
/-- Every packet position in block 38 has its complete signed return and inverse certificates. -/
theorem generatedSeventhXiShortPacketReturn_block38 : ∀ r : Fin 512,
    let k : Fin 27624 := ⟨19456 + r.val, by omega⟩
    generatedSeventhXiShortPacketInverseIndex (generatedSeventhXiShortPacketImageIndex k) = k ∧
    generatedSeventhXiShortPacketImageIndex (generatedSeventhXiShortPacketInverseIndex k) = k ∧
    generatedSeventhXiShortQImageFast (generatedSeventhXiShortPacketMask k) =
      generatedSeventhXiShortPacketMask (generatedSeventhXiShortPacketImageIndex k) ∧
    (if generatedSeventhXiShortQPhaseFast (generatedSeventhXiShortPacketMask k)
      then (-1 : ℤ) else 1) * generatedSeventhXiShortPacketCoefficient k =
      generatedSeventhXiShortPacketCoefficient (generatedSeventhXiShortPacketImageIndex k) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
