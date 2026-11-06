/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorPacket15

/-! Every original address retains its actual operator binding. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem blocks (q : Fin 128) (k : Fin 16) (m : Fin 256) :
    generatedNinthPauliStateInteger ⟨q.val, by omega⟩ (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) =
      generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
        (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0)
        (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) := by
  fin_cases k
  · exact generatedNinth_pauli_operator_packet_00 q m
  · exact generatedNinth_pauli_operator_packet_01 q m
  · exact generatedNinth_pauli_operator_packet_02 q m
  · exact generatedNinth_pauli_operator_packet_03 q m
  · exact generatedNinth_pauli_operator_packet_04 q m
  · exact generatedNinth_pauli_operator_packet_05 q m
  · exact generatedNinth_pauli_operator_packet_06 q m
  · exact generatedNinth_pauli_operator_packet_07 q m
  · exact generatedNinth_pauli_operator_packet_08 q m
  · exact generatedNinth_pauli_operator_packet_09 q m
  · exact generatedNinth_pauli_operator_packet_10 q m
  · exact generatedNinth_pauli_operator_packet_11 q m
  · exact generatedNinth_pauli_operator_packet_12 q m
  · exact generatedNinth_pauli_operator_packet_13 q m
  · exact generatedNinth_pauli_operator_packet_14 q m
  · exact generatedNinth_pauli_operator_packet_15 q m

/-- Every original integer address retains its exact operator source certificate. -/
theorem generatedNinth_pauli_operator_certificate (q : Fin 128) (n : Fin 4096) :
    generatedNinthPauliStateInteger ⟨q.val, by omega⟩ n =
      generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
        (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0) n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hn] using blocks q k m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
