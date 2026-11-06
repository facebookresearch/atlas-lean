/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedCertificates

/-! Original Pauli/input binding on a bounded chronological address block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every candidate translated state in this block equals its actual signed Q operator. -/
theorem generatedNinth_pauli_operator_packet_07 : ∀ q : Fin 128, ∀ m : Fin 256,
    let n : Fin 4096 := ⟨1792 + m.val, by omega⟩
    generatedNinthPauliStateInteger ⟨q.val, by omega⟩ n =
      generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
        (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0) n := by
  intro q m
  exact generatedNinth_pauli_operator_state_actual q _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
