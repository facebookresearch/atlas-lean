/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliBasisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedCertificates

/-! Original Pauli/input binding on a bounded chronological address block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every candidate basis input in this block retains the original 64 signed source states. -/
theorem generatedNinth_pauli_input_packet_13 : ∀ b : Fin 8, ∀ m : Fin 256,
    let n : Fin 4096 := ⟨3328 + m.val, by omega⟩
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ n =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b) n := by
  intro b m
  exact generatedNinth_pauli_input_state_actual b _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
