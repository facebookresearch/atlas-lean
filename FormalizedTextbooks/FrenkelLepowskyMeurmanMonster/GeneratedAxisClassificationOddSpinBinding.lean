/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddSpinOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinDictionarySum

/-! Binding the actual zero-label Y dictionary to the distinguished Hadamard state. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original zero Golay coefficient label is the zero spin index. -/
theorem generatedOddSpin_label_zero :
    golayLabelCoefficients (⟨0, by decide⟩ : Fin 4096) = 0 := by
  decide +kernel

/-- The original all-one label is the last spin-coordinate basis vector. -/
theorem generatedOddSpin_label_omega :
    golayLabelCoefficients (⟨2048, by decide⟩ : Fin 4096) = Pi.single (11 : Fin 12) 1 := by
  decide +kernel

/-- The distinguished source spin dictionary pair consists exactly of the
indices with zero lower eleven bits. -/
theorem generatedOddSpin_dictionary_zero_iff (t : SpinIndex) :
    spinDictionaryCode t = 0 ↔ generatedOddSpinLow t = 0 := by
  constructor
  · intro h
    have ht := spinDictionaryIndex_cases t
    simp only [h, Fin.val_zero, Nat.zero_add] at ht
    rcases ht with ht | ht
    · rw [ht, generatedOddSpin_label_zero]
      rfl
    · rw [ht, generatedOddSpin_label_omega]
      ext j
      simp [generatedOddSpinLow, Pi.single_apply, Fin.ext_iff]
      omega
  · intro h
    have ht : t = generatedOddSpinInsert 0 (t 11) := by
      ext j
      by_cases hj : j.val = 11
      · have hj' : j = (11 : Fin 12) := Fin.ext hj
        subst j
        change t 11 = (Fin.snoc (α := fun _ : Fin 12 => ZMod 2) 0 (t 11)) 11
        have he : (11 : Fin 12) = Fin.last 11 := by decide +kernel
        rw [he, Fin.snoc_last]
      · let k : Fin 11 := ⟨j.val, by omega⟩
        have hj' : j = k.castSucc := Fin.ext rfl
        rw [hj']
        change t k.castSucc = Fin.snoc (α := fun _ : Fin 12 => ZMod 2) 0 (t 11) k.castSucc
        rw [Fin.snoc_castSucc]
        exact congrFun h k
    have hz : spinDictionaryCode (0 : SpinIndex) = 0 := by
      simpa only [Fin.val_zero, generatedOddSpin_label_zero]
        using spinDictionaryCode_low (0 : Fin 2048)
    have ho : spinDictionaryCode (Pi.single (11 : Fin 12) 1) = 0 := by
      simpa only [Fin.val_zero, Nat.zero_add, generatedOddSpin_label_omega]
        using spinDictionaryCode_high (0 : Fin 2048)
    have he : ∀ z : ZMod 2, generatedOddSpinInsert 0 z = 0 ∨
        generatedOddSpinInsert 0 z = Pi.single (11 : Fin 12) 1 := by decide +kernel
    rw [ht]
    rcases he (t 11) with he | he <;> rwa [he]

/-- The actual zero-label Y tensor is the distinguished Hadamard state in one column. -/
theorem generatedOddSpin_Y_binding (i : Fin 24) (t : SpinIndex) (j : Fin 24) :
    trialityYTensor 0 i t j = generatedOddSpinState 0 1 0 t *
      (if j = i then 1 else 0) / Real.sqrt 2 := by
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  simp only [trialityYTensor, Fin.val_zero, hm, Nat.zero_testBit, Bool.false_eq_true, ite_false,
    mul_one, generatedOddSpin_dictionary_zero_iff, generatedOddSpinState,
    zero_add, one_mul]
  split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
