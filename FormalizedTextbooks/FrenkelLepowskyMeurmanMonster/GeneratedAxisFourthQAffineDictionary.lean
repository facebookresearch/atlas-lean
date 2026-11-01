/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityPairTensor

/-! The original two-point Y dictionary on a four-point affine spin plane. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original dictionary fibre consists of the two actual labels differing in bit eleven. -/
theorem generatedFourthQ_dictionary_fiber (d : Fin 2048) (t : SpinIndex) :
    spinDictionaryCode t = d ↔
      t = golayLabelCoefficients ⟨d.val, by omega⟩ ∨
        t = golayLabelCoefficients ⟨d.val, by omega⟩ + Pi.single 11 1 := by
  constructor
  · intro hd
    rcases spinDictionaryIndex_cases t with ht | ht
    · left
      simpa only [hd] using ht
    · right
      simpa only [hd, ← golayLabel_low_add_omega d] using ht
  · rintro (rfl | rfl)
    · exact spinDictionaryCode_low d
    · rw [spinDictionaryCode_add_omega, spinDictionaryCode_low]

private theorem fourth_affine_cancel (t a : SpinIndex) : (t + a) + a = t := by
  rw [add_assoc, ZModModule.add_self, add_zero]

/-- Two low dictionary fibres spanning a four-point plane carry exactly its affine character. -/
theorem generatedFourthQ_affine_dictionary_state
    (S : Submodule (ZMod 2) SpinIndex) (d e : Fin 2048) (v b : SpinIndex)
    (he : golayLabelCoefficients ⟨e.val, by omega⟩ =
      golayLabelCoefficients ⟨d.val, by omega⟩ + v)
    (hS : ∀ u, u ∈ S ↔ u = 0 ∨ u = v ∨ u = Pi.single 11 1 ∨ u = v + Pi.single 11 1)
    (hb : spinDot b (Pi.single 11 1) = 1) (t : SpinIndex) :
    generatedAxisFourthQAffineSpinState S
        (golayLabelCoefficients ⟨d.val, by omega⟩) b t =
      if spinDictionaryCode t = d then qSign (t 11)
      else if spinDictionaryCode t = e then qSign (spinDot b v) * qSign (t 11) else 0 := by
  classical
  let a : SpinIndex := golayLabelCoefficients ⟨d.val, by omega⟩
  have ha : a 11 = 0 := golayLabel_low_last d
  have hv : v 11 = 0 := by
    have hh := congrFun he 11
    simp only [golayLabel_low_last, Pi.add_apply, zero_add] at hh
    exact hh.symm
  have hmemv : v ∈ S := (hS v).mpr (Or.inr (Or.inl rfl))
  have hmemo : (Pi.single 11 1 : SpinIndex) ∈ S :=
    (hS _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hmemvo : v + Pi.single 11 1 ∈ S := S.add_mem hmemv hmemo
  by_cases hd : spinDictionaryCode t = d
  · rw [ite_eq_left hd]
    rcases (generatedFourthQ_dictionary_fiber d t).mp hd with ht | ht
    · rw [ht, generatedAxisFourthQAffineSpinState_base, golayLabel_low_last, qSign_zero]
    · have hx : (a + Pi.single 11 1) + a = Pi.single 11 1 := by
        calc
          _ = (a + a) + Pi.single 11 1 := by abel
          _ = Pi.single 11 1 := by rw [ZModModule.add_self, zero_add]
      change t = a + Pi.single 11 1 at ht
      rw [ht]
      change (if (a + Pi.single 11 1) + a ∈ S then
        qSign (spinDot b ((a + Pi.single 11 1) + a)) else 0) = _
      rw [hx, ite_eq_left hmemo, hb]
      simp only [Pi.add_apply, ha, Pi.single_eq_same, zero_add]
  · rw [ite_eq_right hd]
    by_cases hd' : spinDictionaryCode t = e
    · rw [ite_eq_left hd']
      rcases (generatedFourthQ_dictionary_fiber e t).mp hd' with ht | ht
      · rw [ht, he]
        have hx : (a + v) + a = v := by
          calc
            _ = (a + a) + v := by abel
            _ = v := by rw [ZModModule.add_self, zero_add]
        change (if (a + v) + a ∈ S then qSign (spinDot b ((a + v) + a)) else 0) = _
        rw [hx, ite_eq_left hmemv]
        simp only [Pi.add_apply, golayLabel_low_last, hv, zero_add, qSign_zero, mul_one]
      · rw [ht, he]
        have hx : ((a + v) + Pi.single 11 1) + a = v + Pi.single 11 1 := by
          calc
            _ = (a + a) + (v + Pi.single 11 1) := by abel
            _ = v + Pi.single 11 1 := by rw [ZModModule.add_self, zero_add]
        change (if ((a + v) + Pi.single 11 1) + a ∈ S then
          qSign (spinDot b (((a + v) + Pi.single 11 1) + a)) else 0) = _
        rw [hx, ite_eq_left hmemvo, spinDot_add_right, hb, qSign_add]
        simp only [Pi.add_apply, golayLabel_low_last, hv, Pi.single_eq_same, zero_add]
    · rw [ite_eq_right hd']
      have hn : t + a ∉ S := by
        intro hm
        have ht : t = (t + a) + a := (fourth_affine_cancel t a).symm
        rcases (hS _).mp hm with hz | hv' | ho | hvo
        · apply hd
          rw [ht, hz, zero_add]
          exact spinDictionaryCode_low d
        · apply hd'
          rw [ht, hv', add_comm v a, ← he]
          exact spinDictionaryCode_low e
        · apply hd
          rw [ht, ho, add_comm, spinDictionaryCode_add_omega]
          exact spinDictionaryCode_low d
        · apply hd'
          have hx : (v + Pi.single 11 1) + a = (a + v) + Pi.single 11 1 := by abel
          rw [ht, hvo, hx, ← he, spinDictionaryCode_add_omega]
          exact spinDictionaryCode_low e
      exact ite_eq_right hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
