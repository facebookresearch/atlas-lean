/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliBasisData

/-! Exact candidate common-support address coverage in block2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Check only256 original addresses against all256 literal candidate support labels.
/-- Every supported address in this block occurs in the actual finite support-label table. -/
theorem generatedNinth_pauli_support_address_packet_02 : ∀ v : Fin 256,
    let n : Fin 4096 := ⟨512 + v.val, by omega⟩
    (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit (n.val % 256) = true →
      ∃ m : Fin 256, generatedNinthPauliSupportLabel m = n := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
