/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact code and all-one translation constraints on octad×odd preferred products. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddQSelector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCodeSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddSpinPair

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem spinDictionaryCode_add_smul_omega (t : SpinIndex) (c : ZMod 2) :
    spinDictionaryCode (t+c • Pi.single 11 1) = spinDictionaryCode t := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide +kernel) c with rfl | rfl
  · simp only [zero_smul, add_zero]
  · simp only [one_smul, spinDictionaryCode_add_omega]

/-- The actual dictionary selector fixes the translated code up to its Ω coefficient. -/
theorem octadSpinSelector_low_sum (o : Fin 759) (d f : Fin 2048)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    octadSpinLow d = octadSpinLow f + octadSpinCode o +
      (octadSpinCode o) 11 • Pi.single 11 1 := by
  have ht := spinDictionaryIndex_low_omega (octadSpinLow f + octadSpinCode o)
  rw [hd] at ht
  have hz : (octadSpinLow f + octadSpinCode o) 11 = (octadSpinCode o) 11 := by
    simp only [Pi.add_apply, octadSpinLow, golayLabel_low_last, zero_add]
  rw [hz] at ht
  have he := congrArg (fun t : SpinIndex => t+(octadSpinCode o) 11 • Pi.single 11 1) ht
  simpa only [add_assoc, ← add_smul, ZModModule.add_self, zero_smul, add_zero] using he.symm

/-- Under the exact code selector, Q translation equality is one explicit Ω parity equation. -/
theorem griessOctadOdd_translation_selector (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    spinTranslation (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inr (d,i)))) =
      spinTranslation (griessShortQ (Sum.inr (Sum.inr (f,j)))) ↔
    griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
      griessOddOmegaCoefficient f j + (octadSpinCode o) 11 = 0 := by
  rw [spinTranslation_mul, griessOctad_translation, griessOdd_translation,
    griessOdd_translation]
  change (octadSpinCode o + griessOctadOmegaCoefficient e • Pi.single 11 1) +
    (octadSpinLow d + griessOddOmegaCoefficient d i • Pi.single 11 1) =
      octadSpinLow f + griessOddOmegaCoefficient f j • Pi.single 11 1 ↔ _
  rw [octadSpinSelector_low_sum o d f hd]
  have hl : (octadSpinCode o + griessOctadOmegaCoefficient e • Pi.single 11 1) +
      (octadSpinLow f + octadSpinCode o + (octadSpinCode o) 11 • Pi.single 11 1 +
        griessOddOmegaCoefficient d i • Pi.single 11 1) =
      octadSpinLow f + (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
        (octadSpinCode o) 11) • Pi.single 11 1 := by
    rw [add_smul, add_smul]
    calc
      _ = octadSpinLow f + ((octadSpinCode o+octadSpinCode o) +
        (griessOctadOmegaCoefficient e • Pi.single 11 1 +
          griessOddOmegaCoefficient d i • Pi.single 11 1 +
          (octadSpinCode o) 11 • Pi.single 11 1)) := by abel
      _ = _ := by rw [ZModModule.add_self, zero_add]
  rw [hl,add_left_cancel_iff]
  constructor
  · intro h
    have he := congrArg (fun t : SpinIndex => t 11) h
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at he
    calc
      _ = (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
        (octadSpinCode o) 11) + griessOddOmegaCoefficient f j := by abel
      _ = _ := by rw [he,ZModModule.add_self]
  · intro h
    have he : griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
        (octadSpinCode o) 11 = griessOddOmegaCoefficient f j := by
      have hh := congrArg (fun x : ZMod 2 => x+griessOddOmegaCoefficient f j) h
      have hs : griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
          griessOddOmegaCoefficient f j + (octadSpinCode o) 11 +
          griessOddOmegaCoefficient f j =
          griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
            (octadSpinCode o) 11 := by
        calc
          _ = griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
              (octadSpinCode o) 11 +
              (griessOddOmegaCoefficient f j+griessOddOmegaCoefficient f j) := by abel
          _ = _ := by rw [ZModModule.add_self, add_zero]
      simpa only [hs,zero_add] using hh
    rw [he]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
