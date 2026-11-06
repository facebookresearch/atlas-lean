/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportWordPacket16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportAddressPacket15

/-! Chronological finite certificates imply exact common support of all candidate states. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every sign or magnitude plane is contained in the stated common support. -/
theorem generatedNinth_pauli_state_words_support :
    ∀ s : Fin 136, ∀ p : Fin 3, ∀ b : Fin 16,
      (generatedNinthPauliStateWords s p b &&& generatedNinthPauliSupportWords b) =
        generatedNinthPauliStateWords s p b := by
  intro s p b
  let k : Fin 17 := ⟨s.val / 8, by omega⟩
  let v : Fin 8 := ⟨s.val % 8, by omega⟩
  have h : ∀ k : Fin 17, ∀ v : Fin 8,
      let t : Fin 136 := ⟨8 * k.val + v.val, by omega⟩
      (generatedNinthPauliStateWords t p b &&& generatedNinthPauliSupportWords b) =
        generatedNinthPauliStateWords t p b := by
    intro k v
    fin_cases k
    · exact generatedNinth_pauli_support_word_packet_00 v p b
    · exact generatedNinth_pauli_support_word_packet_01 v p b
    · exact generatedNinth_pauli_support_word_packet_02 v p b
    · exact generatedNinth_pauli_support_word_packet_03 v p b
    · exact generatedNinth_pauli_support_word_packet_04 v p b
    · exact generatedNinth_pauli_support_word_packet_05 v p b
    · exact generatedNinth_pauli_support_word_packet_06 v p b
    · exact generatedNinth_pauli_support_word_packet_07 v p b
    · exact generatedNinth_pauli_support_word_packet_08 v p b
    · exact generatedNinth_pauli_support_word_packet_09 v p b
    · exact generatedNinth_pauli_support_word_packet_10 v p b
    · exact generatedNinth_pauli_support_word_packet_11 v p b
    · exact generatedNinth_pauli_support_word_packet_12 v p b
    · exact generatedNinth_pauli_support_word_packet_13 v p b
    · exact generatedNinth_pauli_support_word_packet_14 v p b
    · exact generatedNinth_pauli_support_word_packet_15 v p b
    · exact generatedNinth_pauli_support_word_packet_16 v p b
  have ht : (⟨8 * k.val + v.val, by omega⟩ : Fin 136) = s := Fin.ext (by dsimp [k, v]; omega)
  have htval : 8 * k.val + v.val = s.val := by dsimp [k, v]; omega
  simpa only [ht, htval] using h k v

/-- Every candidate state vanishes outside the common chronological support. -/
theorem generatedNinth_pauli_state_zero (s : Fin 136) (n : Fin 4096)
    (hn : (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit
      (n.val % 256) = false) : generatedNinthPauliStateInteger s n = 0 := by
  have hp (p : Fin 3) :
      (generatedNinthPauliStateWords s p ⟨n.val / 256, by omega⟩).testBit
        (n.val % 256) = false := by
    have h := congrArg (fun v : ℕ => v.testBit (n.val % 256))
      (generatedNinth_pauli_state_words_support s p ⟨n.val / 256, by omega⟩)
    rw [Nat.testBit_and, hn] at h
    simpa using h.symm
  simp [generatedNinthPauliStateInteger, hp]

/-- Every supported address appears in the finite chronological support table. -/
theorem generatedNinth_pauli_support_complete : ∀ n : Fin 4096,
    (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit (n.val % 256) = true →
      ∃ m : Fin 256, generatedNinthPauliSupportLabel m = n := by
  intro n hn
  let k : Fin 16 := ⟨n.val / 256, by omega⟩
  let v : Fin 256 := ⟨n.val % 256, by omega⟩
  have h : ∀ k : Fin 16, ∀ v : Fin 256,
      let t : Fin 4096 := ⟨256 * k.val + v.val, by omega⟩
      (generatedNinthPauliSupportWords ⟨t.val / 256, by omega⟩).testBit (t.val % 256) = true →
        ∃ m : Fin 256, generatedNinthPauliSupportLabel m = t := by
    intro k v
    fin_cases k
    · exact generatedNinth_pauli_support_address_packet_00 v
    · exact generatedNinth_pauli_support_address_packet_01 v
    · exact generatedNinth_pauli_support_address_packet_02 v
    · exact generatedNinth_pauli_support_address_packet_03 v
    · exact generatedNinth_pauli_support_address_packet_04 v
    · exact generatedNinth_pauli_support_address_packet_05 v
    · exact generatedNinth_pauli_support_address_packet_06 v
    · exact generatedNinth_pauli_support_address_packet_07 v
    · exact generatedNinth_pauli_support_address_packet_08 v
    · exact generatedNinth_pauli_support_address_packet_09 v
    · exact generatedNinth_pauli_support_address_packet_10 v
    · exact generatedNinth_pauli_support_address_packet_11 v
    · exact generatedNinth_pauli_support_address_packet_12 v
    · exact generatedNinth_pauli_support_address_packet_13 v
    · exact generatedNinth_pauli_support_address_packet_14 v
    · exact generatedNinth_pauli_support_address_packet_15 v
  have ht : (⟨256 * k.val + v.val, by omega⟩ : Fin 4096) = n := Fin.ext (by dsimp [k, v]; omega)
  have htval : 256 * k.val + v.val = n.val := by dsimp [k, v]; omega
  have he :
      (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit
        (n.val % 256) = true →
          ∃ m : Fin 256, generatedNinthPauliSupportLabel m = n := by
    simpa only [ht, htval] using h k v
  exact he hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
