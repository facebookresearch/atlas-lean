/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputPacket15

/-! All chronological signed Q sums recover the candidate integer middle columns. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The specified signed Q sum gives every exact candidate middle-column numerator. -/
theorem generatedNinth_pauli_output_certificate (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliOutputFast b n =
      generatedNinthPauliInputDenominator b * generatedNinthPauliMiddleInteger b n := by
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let v : Fin 256 := ⟨n.val % 256, by omega⟩
  have h : ∀ k : Fin 16, ∀ v : Fin 256,
      let t : Fin 4096 := ⟨256 * k.val + v.val, by omega⟩
      generatedNinthPauliOutputFast b t =
        generatedNinthPauliInputDenominator b * generatedNinthPauliMiddleInteger b t := by
    intro k v
    fin_cases k
    · exact generatedNinth_pauli_output_packet_00 b v
    · exact generatedNinth_pauli_output_packet_01 b v
    · exact generatedNinth_pauli_output_packet_02 b v
    · exact generatedNinth_pauli_output_packet_03 b v
    · exact generatedNinth_pauli_output_packet_04 b v
    · exact generatedNinth_pauli_output_packet_05 b v
    · exact generatedNinth_pauli_output_packet_06 b v
    · exact generatedNinth_pauli_output_packet_07 b v
    · exact generatedNinth_pauli_output_packet_08 b v
    · exact generatedNinth_pauli_output_packet_09 b v
    · exact generatedNinth_pauli_output_packet_10 b v
    · exact generatedNinth_pauli_output_packet_11 b v
    · exact generatedNinth_pauli_output_packet_12 b v
    · exact generatedNinth_pauli_output_packet_13 b v
    · exact generatedNinth_pauli_output_packet_14 b v
    · exact generatedNinth_pauli_output_packet_15 b v
  have ht : (⟨256 * k.val + v.val, by omega⟩ : Fin 4096) = n := Fin.ext (by dsimp [k, v]; omega)
  have htval : 256 * k.val + v.val = n.val := by dsimp [k, v]; omega
  simpa only [ht, htval] using h k v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
