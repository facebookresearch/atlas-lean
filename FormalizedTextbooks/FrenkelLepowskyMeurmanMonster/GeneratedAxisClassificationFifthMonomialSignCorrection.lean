/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignTensor

/-! Exact Pauli correction of the actual source sign-word Y states. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The literal Golay sign at a physical coordinate, as an actual binary phase. -/
def generatedFifthYMaskPhase (d : Fin 2048) (i : Fin 24) : ZMod 2 :=
  if (golayEncodedMask d.val).testBit i.val then 1 else 0

private theorem mask_sign (d : Fin 2048) (i : Fin 24) :
    (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) =
      qSign (generatedFifthYMaskPhase d i) := by
  cases hb : (golayEncodedMask d.val).testBit i.val <;>
    simp only [generatedFifthYMaskPhase, hb, Bool.false_eq_true, ite_false, ite_true,
      qSign_zero, qSign_one]

/-- The complete original Y-state transport follows from checked low labels and exact phases. -/
theorem generatedFifth_sign_corrected_Y (q : Q) (d e : Fin 2048) (h α : ZMod 2)
    (he : generatedFifthSpinLow d + spinTranslation q =
      generatedFifthSpinLow e + h • (Pi.single 11 1 : SpinIndex))
    (ho : spinDot (spinModulation q) (Pi.single 11 1) = 0)
    (i j : Fin 24)
    (hp : spinPhase q (generatedFifthSpinLow d) + spinTranslation q 11 +
      generatedFifthYMaskPhase e i = α + generatedFifthYMaskPhase d i) :
    spinRepresentation q (fun t => trialityYTensor e i t j) =
      fun t => qSign α * trialityYTensor d i t j := by
  ext t
  rw [monsterMonomialSpinRepresentation_apply]
  have hd := generatedFifth_sign_dictionary_translate (spinTranslation q) e d h he t
  by_cases ht : spinDictionaryCode t = d
  · have hs := hd.mpr ht
    have hc := congrArg qSign hp
    rw [qSign_add, qSign_add, qSign_add, ← mask_sign e i, ← mask_sign d i] at hc
    rw [generatedFifth_sign_phase_dictionary q d t ho ht]
    simp only [trialityYTensor, hs, ht, ite_true, mul_one, Pi.add_apply]
    rw [qSign_add]
    calc
      _ = (qSign (spinPhase q (generatedFifthSpinLow d)) *
          qSign (spinTranslation q 11) *
          (if (golayEncodedMask e.val).testBit i.val then -1 else 1)) *
            (qSign (t 11) * (if j = i then 1 else 0) / Real.sqrt 2) := by ring
      _ = _ := by rw [hc]; ring
  · have hs : spinDictionaryCode (t + spinTranslation q) ≠ e := fun hn => ht (hd.mp hn)
    simp only [trialityYTensor, ht, hs, ite_false, mul_zero, zero_mul, zero_div]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
