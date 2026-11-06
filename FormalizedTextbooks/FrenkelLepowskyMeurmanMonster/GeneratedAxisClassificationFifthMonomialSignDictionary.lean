/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQTranslation

/-! Ordinary dictionary quotient transport needed for exact source sign operators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem spin_add_self (a : SpinIndex) : a + a = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (a i)

/-- A dictionary label is exactly its two genuine all-one spin representatives. -/
theorem generatedFifth_sign_dictionary_eq (t : SpinIndex) (d : Fin 2048) :
    spinDictionaryCode t = d ↔ ∃ b : ZMod 2,
      t = generatedFifthSpinLow d + b • (Pi.single 11 1 : SpinIndex) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := generatedFifth_spin_dictionary_decomposition t
    exact ⟨b, by simpa only [h] using hb⟩
  · rintro ⟨b, rfl⟩
    have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
    rcases hb with rfl | rfl
    · simp only [zero_smul, add_zero, generatedFifth_spin_low_dictionary]
    · simp only [one_smul, spinDictionaryCode_add_omega, generatedFifth_spin_low_dictionary]

private theorem translate_dictionary_forward (a : SpinIndex) (d e : Fin 2048) (h : ZMod 2)
    (he : generatedFifthSpinLow e + a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex)) (t : SpinIndex)
    (ht : spinDictionaryCode (t + a) = d) : spinDictionaryCode t = e := by
  let w : SpinIndex := Pi.single 11 1
  have hd : generatedFifthSpinLow d = generatedFifthSpinLow e + a + h • w := by
    calc
      _ = (generatedFifthSpinLow d + h • w) + h • w := by
        rw [add_assoc, spin_add_self, add_zero]
      _ = (generatedFifthSpinLow e + a) + h • w := by rw [he]
  obtain ⟨b, hb⟩ := (generatedFifth_sign_dictionary_eq (t + a) d).mp ht
  apply (generatedFifth_sign_dictionary_eq t e).mpr
  refine ⟨b + h, ?_⟩
  calc
    t = (t + a) + a := by rw [add_assoc, spin_add_self, add_zero]
    _ = (generatedFifthSpinLow d + b • w) + a := by rw [hb]
    _ = ((generatedFifthSpinLow e + a + h • w) + b • w) + a := by rw [hd]
    _ = generatedFifthSpinLow e + (b + h) • w + (a + a) := by rw [add_smul]; abel
    _ = _ := by rw [spin_add_self, add_zero]

/-- A checked low-label translation transports the complete actual dictionary selector. -/
theorem generatedFifth_sign_dictionary_translate (a : SpinIndex) (d e : Fin 2048)
    (h : ZMod 2) (he : generatedFifthSpinLow e + a =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex)) (t : SpinIndex) :
    spinDictionaryCode (t + a) = d ↔ spinDictionaryCode t = e := by
  constructor
  · exact translate_dictionary_forward a d e h he t
  · intro ht
    have hd : generatedFifthSpinLow d + a =
        generatedFifthSpinLow e + h • (Pi.single 11 1 : SpinIndex) := by
      let w : SpinIndex := Pi.single 11 1
      have hd0 : generatedFifthSpinLow d = generatedFifthSpinLow e + a + h • w := by
        calc
          _ = (generatedFifthSpinLow d + h • w) + h • w := by
            rw [add_assoc, spin_add_self, add_zero]
          _ = (generatedFifthSpinLow e + a) + h • w := by rw [he]
      calc
        _ = (generatedFifthSpinLow e + a + h • w) + a := by rw [hd0]
        _ = generatedFifthSpinLow e + h • w + (a + a) := by abel
        _ = _ := by rw [spin_add_self, add_zero]
    have hr := translate_dictionary_forward a e d h hd (t + a)
    rw [add_assoc, spin_add_self, add_zero] at hr
    exact hr ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
