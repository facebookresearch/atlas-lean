/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityMixedSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerCyclicPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductSupport
/-! Exact odd-short spin pairings in the mixed XYZ cubic.

The odd lift's theta self-character cancels its quarter-weight correction.
Its coordinate character leaves precisely the selected bit of the other
code word. The two-code addition condition is tested in the actual lower
source representatives; the all-one correction has no effect on the
source label. Thus the pairing is explicit when addition holds and zero
otherwise, with no spin compatibility hypothesis.
Source: Seysen, arXiv:2002.10921v3, Table 5 and §8.1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
-- The spin dictionaries use matrix-valued function abbreviations.
set_option backward.isDefEq.respectTransparency false

lemma golayEncoder_low_bit (d : Fin 2048) (j : Fin 24) :
    golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) j =
      (if (golayEncodedMask d.val).testBit j.val then 1 else 0 : ZMod 2) := by
  have h := sourceCodeInteger_cast_encoder (⟨d.val, by omega⟩ : Fin 4096) j
  simpa only [sourceCodeInteger, Int.cast_ite, Int.cast_one, Int.cast_zero] using h.symm

lemma golayEncoder_low_qSign (d : Fin 2048) (j : Fin 24) :
    qSign (golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) j) =
      (if (golayEncodedMask d.val).testBit j.val then -1 else 1 : ℝ) := by
  rw [golayEncoder_low_bit]
  cases h : (golayEncodedMask d.val).testBit j.val <;> simp [qSign_zero, qSign_one]

lemma griessOddOmegaCoefficient_quarter (d : Fin 2048) (j : Fin 24) :
    griessOddOmegaCoefficient d j =
      (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
        golayEncoder (golayLabelCoefficients ⟨d.val, by omega⟩) j := by
  have hweight : (if golayMaskWeight (golayEncodedMask d.val) % 8 = 0 then 0 else 1 :
      ZMod 2) = (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
    have hw := golayEncodedMask_weights (⟨d.val, by omega⟩ : Fin 4096)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw | hw | hw | hw <;> rw [hw] <;> norm_num <;> decide
  rw [griessOddOmegaCoefficient, hweight, golayEncoder_low_bit]

lemma griessOdd_translation_last (d : Fin 2048) (j : Fin 24) :
    spinTranslation (griessShortQ (Sum.inr (Sum.inr (d,j)))) 11 =
      griessOddOmegaCoefficient d j := by
  rw [griessOdd_translation]
  simp only [Pi.add_apply, golayLabel_low_last, Pi.smul_apply, Pi.single_apply,
    ite_true, smul_eq_mul, mul_one, zero_add]

lemma golayCoordinate_spinDot (j : Fin 24) (a : SpinIndex) :
    spinDot (fun k => (golayGeneratorBit k j : ZMod 2)) a = golayEncoder a j := by
  unfold spinDot
  change (∑ k, (golayGeneratorBit k j : ZMod 2) * a k) =
    ∑ k, a k * (golayGeneratorBit k j : ZMod 2)
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma griessOdd_YZ_phase (d e f : Fin 2048) (j : Fin 24)
    (hf : golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ = golayLabelCoefficients ⟨f.val, by omega⟩) :
    spinPhase (griessShortQ (Sum.inr (Sum.inr (d,j))))
        (golayLabelCoefficients ⟨f.val, by omega⟩) +
      spinTranslation (griessShortQ (Sum.inr (Sum.inr (d,j)))) 11 =
    spinDot (sourceWordTheta ⟨d.val, by omega⟩) (golayLabelCoefficients ⟨e.val, by omega⟩) +
      golayEncoder (golayLabelCoefficients ⟨e.val, by omega⟩) j := by
  simp only [spinPhase, griessShortQ_coeff, zero_add]
  rw [griessOdd_modulation, griessOdd_translation_last, spinDot_add_left,
    golayCoordinate_spinDot, griessOddOmegaCoefficient_quarter, ← hf,
    spinDot_add_right, sourceWordTheta_self_dot, map_add]
  simp only [Pi.add_apply]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero, zero_add]

private lemma binary_spin_add_self (a : SpinIndex) : a + a = 0 := by
  ext i
  change a i + a i = 0
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

lemma griessOdd_translated_code_iff (d e f : Fin 2048) (j : Fin 24) :
    spinDictionaryCode (golayLabelCoefficients ⟨f.val, by omega⟩ +
      spinTranslation (griessShortQ (Sum.inr (Sum.inr (d,j))))) = e ↔
    golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ = golayLabelCoefficients ⟨f.val, by omega⟩ := by
  rw [griessOdd_translation, ← add_assoc, spinDictionaryCode_add_omega_smul,
    spinDictionaryCode_low_add_iff]
  constructor
  · intro h
    rw [← h]
    calc
      _ = golayLabelCoefficients ⟨f.val, by omega⟩ +
        (golayLabelCoefficients ⟨d.val, by omega⟩ +
          golayLabelCoefficients ⟨d.val, by omega⟩) := by abel
      _ = _ := by rw [binary_spin_add_self, add_zero]
  · intro h
    rw [← h]
    calc
      _ = golayLabelCoefficients ⟨e.val, by omega⟩ +
        (golayLabelCoefficients ⟨d.val, by omega⟩ +
          golayLabelCoefficients ⟨d.val, by omega⟩) := by abel
      _ = _ := by rw [binary_spin_add_self, add_zero]

/-- The actual odd-short Y/Z spin contraction under source code addition. -/
theorem trialitySpinPair_odd_YZ (d e f : Fin 2048) (j k l : Fin 24)
    (hf : golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ = golayLabelCoefficients ⟨f.val, by omega⟩) :
    (∑ t, spinOperator (griessShortQ (Sum.inr (Sum.inr (d,j))))
        (fun v => trialityYTensor e k v k) t * trialityZTensor f l t l) =
      qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) *
        qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩)
          (golayLabelCoefficients ⟨e.val, by omega⟩)) *
        (if (golayEncodedMask e.val).testBit j.val then -1 else 1) *
        (if (golayEncodedMask e.val).testBit k.val then -1 else 1) := by
  rw [trialitySpinPair_YZ _ (griessOdd_modulation_last d j) e f k l,
    griessOdd_YZ_phase d e f j hf, qSign_add, golayEncoder_low_qSign]
  have hcode := (griessOdd_translated_code_iff d e f j).mpr hf
  rw [hcode]
  simp only [ite_true, mul_one]
  ring

/-- The contraction vanishes when the actual source labels do not add. -/
theorem trialitySpinPair_odd_YZ_zero (d e f : Fin 2048) (j k l : Fin 24)
    (hf : golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ ≠ golayLabelCoefficients ⟨f.val, by omega⟩) :
    (∑ t, spinOperator (griessShortQ (Sum.inr (Sum.inr (d,j))))
        (fun v => trialityYTensor e k v k) t * trialityZTensor f l t l) = 0 := by
  rw [trialitySpinPair_YZ _ (griessOdd_modulation_last d j) e f k l]
  have hcode := mt (griessOdd_translated_code_iff d e f j).mp hf
  simp only [hcode, ite_false, mul_zero]

/-- The complete mixed spin contraction, including its code-addition indicator. -/
theorem trialitySpinPair_odd_YZ_all (d e f : Fin 2048) (j k l : Fin 24) :
    (∑ t, spinOperator (griessShortQ (Sum.inr (Sum.inr (d,j))))
        (fun v => trialityYTensor e k v k) t * trialityZTensor f l t l) =
      qSign (golayMaskWeight (golayEncodedMask f.val) / 4 : ℕ) *
        qSign (spinDot (sourceWordTheta ⟨d.val, by omega⟩)
          (golayLabelCoefficients ⟨e.val, by omega⟩)) *
        (if (golayEncodedMask e.val).testBit j.val then -1 else 1) *
        (if (golayEncodedMask e.val).testBit k.val then -1 else 1) *
        (if golayLabelCoefficients ⟨d.val, by omega⟩ +
          golayLabelCoefficients ⟨e.val, by omega⟩ =
            golayLabelCoefficients ⟨f.val, by omega⟩ then 1 else 0) := by
  by_cases hf : golayLabelCoefficients ⟨d.val, by omega⟩ +
      golayLabelCoefficients ⟨e.val, by omega⟩ = golayLabelCoefficients ⟨f.val, by omega⟩
  · rw [trialitySpinPair_odd_YZ d e f j k l hf]
    simp only [hf, ite_true, mul_one]
  · rw [trialitySpinPair_odd_YZ_zero d e f j k l hf]
    simp only [hf, ite_false, mul_zero]
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
