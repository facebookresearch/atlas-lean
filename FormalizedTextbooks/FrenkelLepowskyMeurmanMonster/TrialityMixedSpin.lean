/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact mixed spin pairings in the source XYZ dictionary. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinDictionarySum
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityXYZCubic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Pairing against a Z coordinate evaluates exactly its two source spin indices. -/
theorem trialityZTensor_pairing (e : Fin 2048) (k : Fin 24) (F : SpinSpace) :
    (∑ t, F t * trialityZTensor e k t k) =
      qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) / Real.sqrt 2 *
        (F (golayLabelCoefficients ⟨e.val, by omega⟩) +
          F (golayLabelCoefficients ⟨e.val + 2048, by omega⟩)) := by
  have hterm (t : SpinIndex) : F t * trialityZTensor e k t k =
      (qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) / Real.sqrt 2) *
        (if spinDictionaryCode t = e then F t else 0) := by
    by_cases h : spinDictionaryCode t = e
    · simp only [trialityZTensor, h, ite_true, mul_one]
      ring
    · simp [trialityZTensor, h]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_spinDictionaryCode]

/-- An all-one-even spin function has identical values at the two Z indices. -/
theorem trialityZTensor_pairing_even (e : Fin 2048) (k : Fin 24) (F : SpinSpace)
    (heven : ∀ t, F (t + Pi.single 11 1) = F t) :
    (∑ t, F t * trialityZTensor e k t k) =
      2 * qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) / Real.sqrt 2 *
        F (golayLabelCoefficients ⟨e.val, by omega⟩) := by
  rw [trialityZTensor_pairing, ← golayLabel_low_add_omega, heven]
  ring

/-- An odd-modulation Q lift pairs Y with Z through a single actual source spin index. -/
theorem trialitySpinPair_YZ (q : Q) (hq : spinModulation q 11 = 1)
    (d e : Fin 2048) (j k : Fin 24) :
    (∑ t, spinOperator q (fun v => trialityYTensor d j v j) t *
        trialityZTensor e k t k) =
      qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) *
        qSign (spinPhase q (golayLabelCoefficients ⟨e.val, by omega⟩) +
          spinTranslation q 11) *
        (if (golayEncodedMask d.val).testBit j.val then -1 else 1) *
        (if spinDictionaryCode (golayLabelCoefficients ⟨e.val, by omega⟩ +
          spinTranslation q) = d then 1 else 0) := by
  have hy (t : SpinIndex) : trialityYTensor d j (t + trialitySpinOmega) j =
      (-1 : ℝ) * trialityYTensor d j t j := by
    rw [trialitySpinOmega, trialityYTensor_add_omega]
    ring
  have heven (t : SpinIndex) :
      spinOperator q (fun v => trialityYTensor d j v j) (t + Pi.single 11 1) =
        spinOperator q (fun v => trialityYTensor d j v j) t := by
    simpa only [trialitySpinOmega, neg_neg, one_mul] using
      (spinOperator_omega_parity q hq _ (-1) hy t)
  rw [trialityZTensor_pairing_even e k _ heven]
  change 2 * qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) / Real.sqrt 2 *
      (qSign (spinPhase q (golayLabelCoefficients ⟨e.val, by omega⟩)) *
        trialityYTensor d j (golayLabelCoefficients ⟨e.val, by omega⟩ +
          spinTranslation q) j) = _
  simp only [trialityYTensor, Pi.add_apply, golayLabel_low_last, zero_add,
    ite_true, mul_one, qSign_add]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc
    _ = (2 * qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) *
      qSign (spinPhase q (golayLabelCoefficients ⟨e.val, by omega⟩)) *
      qSign (spinTranslation q 11) *
      (if (golayEncodedMask d.val).testBit j.val then -1 else 1) *
      (if spinDictionaryCode (golayLabelCoefficients ⟨e.val, by omega⟩ +
        spinTranslation q) = d then 1 else 0)) / (Real.sqrt 2 * Real.sqrt 2) := by ring
    _ = _ := by rw [hs]; ring

/-- A spin index with zero all-one bit is its actual lower source representative. -/
theorem spinDictionaryCode_eq_low_iff (t : SpinIndex) (e : Fin 2048) (ht : t 11 = 0) :
    spinDictionaryCode t = e ↔ t = golayLabelCoefficients ⟨e.val, by omega⟩ := by
  constructor
  · intro he
    rcases spinDictionaryIndex_cases t with h | h
    · simpa only [he] using h
    · have hh := congrFun h 11
      rw [ht, golayLabel_high_last] at hh
      exact False.elim (zero_ne_one hh)
  · intro he
    rw [he, spinDictionaryCode_low]

/-- Adding two lower source code representatives has no hidden all-one ambiguity. -/
theorem spinDictionaryCode_low_add_iff (d e f : Fin 2048) :
    spinDictionaryCode (golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩) = f ↔
    golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ =
        golayLabelCoefficients ⟨f.val, by omega⟩ := by
  apply spinDictionaryCode_eq_low_iff
  simp only [Pi.add_apply, golayLabel_low_last, zero_add]

/-- The source label of a translated spin index ignores its all-one correction. -/
theorem spinDictionaryCode_add_omega_smul (t : SpinIndex) (c : ZMod 2) :
    spinDictionaryCode (t + c • Pi.single 11 1) = spinDictionaryCode t := by
  have hc : c = 0 ∨ c = 1 := by
    have hv := ZMod.val_lt c
    by_cases hz : c.val = 0
    · exact Or.inl ((ZMod.val_eq_zero c).mp hz)
    · right
      apply ZMod.val_injective 2
      have hval : (1 : ZMod 2).val = 1 := by decide
      rw [hval]
      omega
  rcases hc with rfl | rfl
  · rw [zero_smul, add_zero]
  · rw [one_smul, spinDictionaryCode_add_omega]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
