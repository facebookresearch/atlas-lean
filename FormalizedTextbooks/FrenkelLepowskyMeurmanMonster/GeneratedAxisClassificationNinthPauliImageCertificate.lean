/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImagePacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImagePacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImagePacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImagePacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImagePacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImagePacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImagePacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImagePacket07

/-! Chronological certificates bind every full-phase witness image to the original Q action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every witness image retains the actual translation, modulation and central phase. -/
theorem generatedNinth_pauli_image_certificate (q : Fin 128) :
    generatedNinthQImage (generatedNinthPauliQ (generatedNinthPauliWitnessLabels q 0)
      (generatedNinthPauliWitnessLabels q 1)) = generatedNinthPauliImage q := by
  let k : Fin 8 := ⟨q.val / 16, by omega⟩
  let v : Fin 16 := ⟨q.val % 16, by omega⟩
  have h : ∀ k : Fin 8, ∀ v : Fin 16,
      let n : Fin 128 := ⟨16 * k.val + v.val, by omega⟩
      generatedNinthQImage (generatedNinthPauliQ (generatedNinthPauliWitnessLabels n 0)
        (generatedNinthPauliWitnessLabels n 1)) = generatedNinthPauliImage n := by
    intro k v
    fin_cases k
    · exact generatedNinth_pauli_image_packet_00 v
    · exact generatedNinth_pauli_image_packet_01 v
    · exact generatedNinth_pauli_image_packet_02 v
    · exact generatedNinth_pauli_image_packet_03 v
    · exact generatedNinth_pauli_image_packet_04 v
    · exact generatedNinth_pauli_image_packet_05 v
    · exact generatedNinth_pauli_image_packet_06 v
    · exact generatedNinth_pauli_image_packet_07 v
  have hn : (⟨16 * k.val + v.val, by omega⟩ : Fin 128) = q := Fin.ext (by dsimp [k, v]; omega)
  have hnval : 16 * k.val + v.val = q.val := by dsimp [k, v]; omega
  simpa only [hn, hnval] using h k v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
