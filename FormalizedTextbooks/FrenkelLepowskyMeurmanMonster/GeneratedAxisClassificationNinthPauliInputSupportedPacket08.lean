/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSourceSupport

/-! Original signed source-input values on sixteen complete common-support addresses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check the eight original basis inputs at only sixteen common-support addresses.
/-- Every displayed supported input value is the literal original64-term signed source sum. -/
theorem generatedNinth_pauli_input_supported_packet_08 : ∀ b : Fin 8, ∀ v : Fin 16,
    let m : Fin 256 := ⟨128 + v.val, by omega⟩
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ (generatedNinthPauliSupportLabel m) =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b)
        (generatedNinthPauliSupportLabel m) := by
  simp_rw [generatedNinth_column_input_sparse_fast]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
