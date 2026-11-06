/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCrossPhase

/-! Exact Pauli transport of original Z dictionary states for source sign lifts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Modulation is constant on the two spin representatives of an actual dictionary code. -/
theorem generatedFifth_sign_phase_dictionary (q : Q) (e : Fin 2048) (t : SpinIndex)
    (ho : spinDot (spinModulation q) (Pi.single 11 1) = 0)
    (ht : spinDictionaryCode t = e) :
    spinPhase q t = spinPhase q (generatedFifthSpinLow e) := by
  obtain ⟨b, hb⟩ := (generatedFifth_sign_dictionary_eq t e).mp ht
  rw [hb]
  simp only [spinPhase, spinDot_add_right, spinDot_smul_right, ho, mul_zero, add_zero]

/-- A checked low-label translation and the actual central phase transport every Z column. -/
theorem generatedFifth_sign_Z_tensor (q : Q) (d e : Fin 2048) (h : ZMod 2)
    (he : generatedFifthSpinLow e + spinTranslation q =
      generatedFifthSpinLow d + h • (Pi.single 11 1 : SpinIndex))
    (ho : spinDot (spinModulation q) (Pi.single 11 1) = 0)
    (i j : Fin 24) (t : SpinIndex) :
    spinRepresentation q (fun v => trialityZTensor d i v j) t =
      qSign (spinPhase q (generatedFifthSpinLow e) +
        (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) +
        (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)) * trialityZTensor e i t j := by
  rw [monsterMonomialSpinRepresentation_apply]
  have hd := generatedFifth_sign_dictionary_translate (spinTranslation q) d e h he t
  by_cases ht : spinDictionaryCode t = e
  · have hs := hd.mpr ht
    rw [generatedFifth_sign_phase_dictionary q e t ho ht]
    simp only [trialityZTensor, ht, hs, ite_true, mul_one]
    rw [qSign_add, qSign_add]
    have hc := qSign_sq (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)
    calc
      _ = (qSign (spinPhase q (generatedFifthSpinLow e)) *
          qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          ((if j = i then (1 : ℝ) else 0) / Real.sqrt 2)) *
            (qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ) *
             qSign (golayMaskWeight (golayEncodedMask e.val) / 4 : ℕ)) := by rw [hc]; ring
      _ = _ := by ring
  · have hs : spinDictionaryCode (t + spinTranslation q) ≠ d := fun hn => ht (hd.mp hn)
    simp only [trialityZTensor, ht, hs, ite_false, mul_zero, zero_mul, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
