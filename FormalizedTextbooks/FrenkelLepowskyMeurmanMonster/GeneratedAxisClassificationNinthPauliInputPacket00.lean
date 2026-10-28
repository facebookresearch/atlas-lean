/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliBasisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnInputFast

/-! Original Pauli/input binding on a bounded chronological address block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Bound the original integer operator replay to 256 spin addresses.
/-- Every candidate basis input in this block retains the original 64 signed source states. -/
theorem generatedNinth_pauli_input_packet_00 : ∀ b : Fin 8, ∀ m : Fin 256,
    let n : Fin 4096 := ⟨0 + m.val, by omega⟩
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ n =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b) n := by
  simp_rw [generatedNinth_column_input_sparse_fast]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
