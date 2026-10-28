/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliInputPacket15

/-! Every original address retains its actual input binding. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem blocks (b : Fin 8) (k : Fin 16) (m : Fin 256) :
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩
      (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b)
        (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) := by
  fin_cases k
  · exact generatedNinth_pauli_input_packet_00 b m
  · exact generatedNinth_pauli_input_packet_01 b m
  · exact generatedNinth_pauli_input_packet_02 b m
  · exact generatedNinth_pauli_input_packet_03 b m
  · exact generatedNinth_pauli_input_packet_04 b m
  · exact generatedNinth_pauli_input_packet_05 b m
  · exact generatedNinth_pauli_input_packet_06 b m
  · exact generatedNinth_pauli_input_packet_07 b m
  · exact generatedNinth_pauli_input_packet_08 b m
  · exact generatedNinth_pauli_input_packet_09 b m
  · exact generatedNinth_pauli_input_packet_10 b m
  · exact generatedNinth_pauli_input_packet_11 b m
  · exact generatedNinth_pauli_input_packet_12 b m
  · exact generatedNinth_pauli_input_packet_13 b m
  · exact generatedNinth_pauli_input_packet_14 b m
  · exact generatedNinth_pauli_input_packet_15 b m

/-- Every original integer address retains its exact input source certificate. -/
theorem generatedNinth_pauli_input_certificate (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ n =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b) n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let m : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have hn : (⟨256 * k.val + m.val, by omega⟩ : Fin 4096) = n := by
    apply Fin.ext
    dsimp only [k, m]
    omega
  simpa only [hn] using blocks b k m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
