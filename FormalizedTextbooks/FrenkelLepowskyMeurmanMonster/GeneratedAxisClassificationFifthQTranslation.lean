/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthTensorSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSpinSupport

/-! Genuine fixation of the fifth tensor restricts translation to zero or the all-one word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A low dictionary code has exactly its displayed actual dictionary label. -/
theorem generatedFifth_spin_low_dictionary (d : Fin 2048) :
    spinDictionaryCode (generatedFifthSpinLow d) = d := by
  exact spinDictionaryCode_low d

/-- Every actual spin index consists of its low dictionary label and an all-one bit. -/
theorem generatedFifth_spin_dictionary_decomposition (t : SpinIndex) :
    ∃ b : ZMod 2, t = generatedFifthSpinLow (spinDictionaryCode t) +
      b • (Pi.single 11 1 : SpinIndex) := by
  rcases spinDictionaryIndex_cases t with h | h
  · exact ⟨0, by simpa only [zero_smul, add_zero, generatedFifthSpinLow] using h⟩
  · refine ⟨1, ?_⟩
    rw [one_smul]
    exact h.trans (golayLabel_low_add_omega (spinDictionaryCode t)).symm

/-- Low dictionary representatives have zero all-one coefficient. -/
theorem generatedFifth_spin_low_last (d : Fin 2048) :
    generatedFifthSpinLow d 11 = 0 :=
  (golayLabel_last_zero ⟨d.val, by omega⟩).mpr d.isLt

/-- Among the genuine candidate translations, only the zero low label preserves column 19. -/
theorem generatedFifth_column_signed_period_certificate : ∀ b : ZMod 2, ∀ k : Fin 8,
    (∀ j : Fin 8, ∃ l : Fin 8,
      spinDictionaryCode (generatedFifthSpinLow (generatedFifthColumnLabels j) +
        generatedFifthSpinLow (generatedFifthColumnLabels k) +
          generatedFifthSpinLow (generatedFifthColumnLabels 0) +
            b • (Pi.single 11 1 : SpinIndex)) = generatedFifthColumnLabels l) → k = 0 := by
  intro b k hk
  apply generatedFifth_column_period_certificate k
  intro j
  obtain ⟨l, hl⟩ := hk j
  obtain ⟨h, hh⟩ := generatedFifth_spin_dictionary_decomposition
    (generatedFifthSpinLow (generatedFifthColumnLabels j) +
      generatedFifthSpinLow (generatedFifthColumnLabels k) +
        generatedFifthSpinLow (generatedFifthColumnLabels 0) +
          b • (Pi.single 11 1 : SpinIndex))
  rw [hl] at hh
  have hb : b = h := by
    have he := congrFun hh 11
    simpa only [Pi.add_apply, generatedFifth_spin_low_last, Pi.smul_apply,
      Pi.single_apply, ite_true, smul_eq_mul, mul_one, zero_add] using he
  rw [← hb] at hh
  exact ⟨l, (add_right_cancel hh).symm⟩

/-- Actual tensor fixation forces zero or the original all-one Pauli translation. -/
theorem generatedFifth_tensor_translation (q : Q)
    (hq : ∀ i : Fin 24, spinRepresentation q
      (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i) =
        (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i)) :
    spinTranslation q = 0 ∨ spinTranslation q = Pi.single 11 1 := by
  let t0 := generatedFifthSpinLow (generatedFifthColumnLabels 0)
  have hs (j : Fin 8) :
      (griessConwayEncode generatedFifthAxis).2.2
        (generatedFifthSpinLow (generatedFifthColumnLabels j)) 19 ≠ 0 := by
    rw [generatedFifth_tensor_nonzero_iff, generatedFifth_spin_low_dictionary,
      generatedFifth_column_labels_certificate]
    exact ⟨j, rfl⟩
  have hp (t : SpinIndex) := generatedSpinSupport_fixed_translation q
    (fun u => (griessConwayEncode generatedFifthAxis).2.2 u 19) (hq 19) t
  have ht := (hp t0).mpr (hs 0)
  rw [generatedFifth_tensor_nonzero_iff, generatedFifth_column_labels_certificate] at ht
  obtain ⟨k, hk⟩ := ht
  obtain ⟨b, hb⟩ := generatedFifth_spin_dictionary_decomposition (t0 + spinTranslation q)
  rw [← hk] at hb
  have ha : spinTranslation q = generatedFifthSpinLow (generatedFifthColumnLabels k) +
      generatedFifthSpinLow (generatedFifthColumnLabels 0) +
        b • (Pi.single 11 1 : SpinIndex) := by
    calc
      _ = t0 + (t0 + spinTranslation q) := by
        rw [← add_assoc, ZModModule.add_self, zero_add]
      _ = _ := by rw [hb]; dsimp [t0]; abel
  have hk0 : k = 0 := by
    apply generatedFifth_column_signed_period_certificate b k
    intro j
    have hj := (hp (generatedFifthSpinLow (generatedFifthColumnLabels j))).mpr (hs j)
    rw [generatedFifth_tensor_nonzero_iff, generatedFifth_column_labels_certificate] at hj
    obtain ⟨l, hl⟩ := hj
    refine ⟨l, ?_⟩
    rw [ha] at hl
    simpa only [add_assoc] using hl.symm
  rw [hk0, ZModModule.add_self, zero_add] at ha
  have hc : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hc with rfl | rfl
  · exact Or.inl (by simpa only [zero_smul] using ha)
  · exact Or.inr (by simpa only [one_smul] using ha)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
