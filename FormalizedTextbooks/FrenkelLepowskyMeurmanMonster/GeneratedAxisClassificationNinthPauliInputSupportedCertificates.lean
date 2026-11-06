/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputSupportedPacket15

/-! Checked original source values on the full common support and exact source zeros outside it
identify every candidate input with its literal original signed source input. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every common-support value is the literal original64-term signed input sum. -/
theorem generatedNinth_pauli_input_supported (b : Fin 8) (m : Fin 256) :
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ (generatedNinthPauliSupportLabel m) =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b)
        (generatedNinthPauliSupportLabel m) := by
  let k : Fin 16 := ⟨m.val / 16, by omega⟩
  let v : Fin 16 := ⟨m.val % 16, by omega⟩
  have h : ∀ k : Fin 16, ∀ v : Fin 16,
      let n : Fin 256 := ⟨16 * k.val + v.val, by omega⟩
      generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ (generatedNinthPauliSupportLabel n) =
        generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b)
          (generatedNinthPauliSupportLabel n) := by
    intro k v
    fin_cases k
    · exact generatedNinth_pauli_input_supported_packet_00 b v
    · exact generatedNinth_pauli_input_supported_packet_01 b v
    · exact generatedNinth_pauli_input_supported_packet_02 b v
    · exact generatedNinth_pauli_input_supported_packet_03 b v
    · exact generatedNinth_pauli_input_supported_packet_04 b v
    · exact generatedNinth_pauli_input_supported_packet_05 b v
    · exact generatedNinth_pauli_input_supported_packet_06 b v
    · exact generatedNinth_pauli_input_supported_packet_07 b v
    · exact generatedNinth_pauli_input_supported_packet_08 b v
    · exact generatedNinth_pauli_input_supported_packet_09 b v
    · exact generatedNinth_pauli_input_supported_packet_10 b v
    · exact generatedNinth_pauli_input_supported_packet_11 b v
    · exact generatedNinth_pauli_input_supported_packet_12 b v
    · exact generatedNinth_pauli_input_supported_packet_13 b v
    · exact generatedNinth_pauli_input_supported_packet_14 b v
    · exact generatedNinth_pauli_input_supported_packet_15 b v
  have ht : (⟨16 * k.val + v.val, by omega⟩ : Fin 256) = m := Fin.ext (by dsimp [k, v]; omega)
  simpa only [ht] using h k v

/-- Every one of the4096 candidate input addresses equals its literal original source sum. -/
theorem generatedNinth_pauli_input_state_actual (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ n =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b) n :=
  generatedNinth_pauli_input_actual_of_supported generatedNinth_pauli_input_supported b n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
