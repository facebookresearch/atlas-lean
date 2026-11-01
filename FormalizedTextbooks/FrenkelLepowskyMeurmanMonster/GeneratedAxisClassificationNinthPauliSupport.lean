/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportStructure
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumPacket15

/-! Exact common support of the candidate Pauli and input integer states. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Candidate input reconstruction uses exact integers and the stated common denominators. -/
theorem generatedNinth_pauli_reconstruction_support : ∀ b : Fin 8, ∀ m : Fin 256,
    generatedNinthPauliInputDenominator b *
      generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ (generatedNinthPauliSupportLabel m) =
        ∑ q : Fin 128, generatedNinthPauliInputCoefficients b q *
          generatedNinthPauliStateInteger ⟨q.val, by omega⟩
            (generatedNinthPauliSupportLabel m) := by
  intro b m
  let k : Fin 16 := ⟨m.val / 16, by omega⟩
  let v : Fin 16 := ⟨m.val % 16, by omega⟩
  have h : ∀ k : Fin 16, ∀ v : Fin 16,
      let n : Fin 256 := ⟨16 * k.val + v.val, by omega⟩
      generatedNinthPauliInputDenominator b *
        generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩
          (generatedNinthPauliSupportLabel n) =
        ∑ q : Fin 128, generatedNinthPauliInputCoefficients b q *
          generatedNinthPauliStateInteger ⟨q.val, by omega⟩
            (generatedNinthPauliSupportLabel n) := by
    intro k v
    fin_cases k
    · exact generatedNinth_pauli_sum_packet_00 b v
    · exact generatedNinth_pauli_sum_packet_01 b v
    · exact generatedNinth_pauli_sum_packet_02 b v
    · exact generatedNinth_pauli_sum_packet_03 b v
    · exact generatedNinth_pauli_sum_packet_04 b v
    · exact generatedNinth_pauli_sum_packet_05 b v
    · exact generatedNinth_pauli_sum_packet_06 b v
    · exact generatedNinth_pauli_sum_packet_07 b v
    · exact generatedNinth_pauli_sum_packet_08 b v
    · exact generatedNinth_pauli_sum_packet_09 b v
    · exact generatedNinth_pauli_sum_packet_10 b v
    · exact generatedNinth_pauli_sum_packet_11 b v
    · exact generatedNinth_pauli_sum_packet_12 b v
    · exact generatedNinth_pauli_sum_packet_13 b v
    · exact generatedNinth_pauli_sum_packet_14 b v
    · exact generatedNinth_pauli_sum_packet_15 b v
  have hn : (⟨16 * k.val + v.val, by omega⟩ : Fin 256) = m := Fin.ext (by dsimp [k, v]; omega)
  have hnval : 16 * k.val + v.val = m.val := by dsimp [k, v]; omega
  simpa only [hn, hnval] using h k v

/-- The exact candidate reconstruction holds at every original spin address. -/
theorem generatedNinth_pauli_reconstruction (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliInputDenominator b *
      generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ n =
        ∑ q : Fin 128, generatedNinthPauliInputCoefficients b q *
          generatedNinthPauliStateInteger ⟨q.val, by omega⟩ n := by
  cases h : (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit (n.val % 256)
  · simp only [generatedNinth_pauli_state_zero _ n h, mul_zero, Finset.sum_const_zero]
  · obtain ⟨m, rfl⟩ := generatedNinth_pauli_support_complete n h
    exact generatedNinth_pauli_reconstruction_support b m

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
