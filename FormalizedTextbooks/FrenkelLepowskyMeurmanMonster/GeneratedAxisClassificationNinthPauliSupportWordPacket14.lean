/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliBasisData

/-! Exact common support of eight candidate state rows in block14. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Check eight state rows, all three magnitude/sign planes and all sixteen address blocks.
/-- Every bit plane in this chronological state block lies in the candidate common support. -/
theorem generatedNinth_pauli_support_word_packet_14 :
    ∀ v : Fin 8, ∀ p : Fin 3, ∀ b : Fin 16,
      let s : Fin 136 := ⟨112 + v.val, by omega⟩
      (generatedNinthPauliStateWords s p b &&& generatedNinthPauliSupportWords b) =
        generatedNinthPauliStateWords s p b := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
