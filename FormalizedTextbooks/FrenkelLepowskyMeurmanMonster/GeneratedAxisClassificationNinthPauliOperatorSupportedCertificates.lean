/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSupportedPacket15

/-! Checked original source values on the full common support and exact source zeros outside it
identify every candidate state with its original signed Pauli operator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every common-support state value is the complete original signed operator value. -/
theorem generatedNinth_pauli_operator_supported (q : Fin 128) (m : Fin 256) :
    generatedNinthPauliStateInteger ⟨q.val, by omega⟩ (generatedNinthPauliSupportLabel m) =
      generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
        (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0)
        (generatedNinthPauliSupportLabel m) := by
  let k : Fin 16 := ⟨m.val / 16, by omega⟩
  let v : Fin 16 := ⟨m.val % 16, by omega⟩
  have h : ∀ k : Fin 16, ∀ v : Fin 16,
      let n : Fin 256 := ⟨16 * k.val + v.val, by omega⟩
      generatedNinthPauliStateInteger ⟨q.val, by omega⟩ (generatedNinthPauliSupportLabel n) =
        generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
          (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0)
          (generatedNinthPauliSupportLabel n) := by
    intro k v
    fin_cases k
    · exact generatedNinth_pauli_operator_supported_packet_00 q v
    · exact generatedNinth_pauli_operator_supported_packet_01 q v
    · exact generatedNinth_pauli_operator_supported_packet_02 q v
    · exact generatedNinth_pauli_operator_supported_packet_03 q v
    · exact generatedNinth_pauli_operator_supported_packet_04 q v
    · exact generatedNinth_pauli_operator_supported_packet_05 q v
    · exact generatedNinth_pauli_operator_supported_packet_06 q v
    · exact generatedNinth_pauli_operator_supported_packet_07 q v
    · exact generatedNinth_pauli_operator_supported_packet_08 q v
    · exact generatedNinth_pauli_operator_supported_packet_09 q v
    · exact generatedNinth_pauli_operator_supported_packet_10 q v
    · exact generatedNinth_pauli_operator_supported_packet_11 q v
    · exact generatedNinth_pauli_operator_supported_packet_12 q v
    · exact generatedNinth_pauli_operator_supported_packet_13 q v
    · exact generatedNinth_pauli_operator_supported_packet_14 q v
    · exact generatedNinth_pauli_operator_supported_packet_15 q v
  have ht : (⟨16 * k.val + v.val, by omega⟩ : Fin 256) = m := Fin.ext (by dsimp [k, v]; omega)
  simpa only [ht] using h k v

/-- All4096 state addresses equal the original signed Pauli action, including exact source zeros. -/
theorem generatedNinth_pauli_operator_state_actual (q : Fin 128) (n : Fin 4096) :
    generatedNinthPauliStateInteger ⟨q.val, by omega⟩ n =
      generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
        (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0) n :=
  generatedNinth_pauli_operator_actual_of_supported generatedNinth_pauli_operator_supported q n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
