/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Parker theta addition for actual octad/odd preferred-Q selectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairQProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ParkerCyclicPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorCoefficients

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The published theta row of the all-one source generator is zero. -/
theorem sourceCodeTheta_omega : sourceCodeTheta (11 : Fin 12) = 0 := by
  ext k
  fin_cases k <;> decide +kernel

/-- The quadratic theta polynomial is unchanged by the all-one generator. -/
theorem sourceCodeThetaPolynomial_add_omega (a : SpinIndex) :
    sourceCodeThetaPolynomial (a + Pi.single 11 1) = sourceCodeThetaPolynomial a := by
  rw [sourceCodeThetaPolynomial_add, sourceCodeThetaPolynomial_single,
    sourceCodeTheta_omega, golay_all_one]
  simp only [mul_one, golaySyndrome_encoder, add_zero]

/-- Arbitrary binary multiples of Ω have the same invariance. -/
theorem sourceCodeThetaPolynomial_add_smul_omega (a : SpinIndex) (c : ZMod 2) :
    sourceCodeThetaPolynomial (a + c • Pi.single 11 1) = sourceCodeThetaPolynomial a := by
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide +kernel) c with rfl | rfl
  · rw [zero_smul, add_zero]
  · rw [one_smul, sourceCodeThetaPolynomial_add_omega]

/-- Actual preferred-Q base equality gives the source code sum up to its
precisely recorded three Ω corrections. -/
theorem griessOctadOddQ_base_translation (o : Fin 759) (e : Fin 64)
    (d : Fin 2048) (i : Fin 24) (f : Fin 2048) (j : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base) :
    golayLabelCoefficients (⟨f.val, by omega⟩ : Fin 4096) =
      golayLabelCoefficients (golayOctadLabel o) +
        golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096) +
      (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
        griessOddOmegaCoefficient f j) • Pi.single 11 1 := by
  have ht : spinTranslation (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))) =
        spinTranslation (griessShortQ (Sum.inr (Sum.inr (f, j)))) := by
    funext k
    exact congrArg (fun v : Multiplicative (Fin 24 → ZMod 2) =>
      toAdd v (Fin.castAdd 12 k)) hb
  rw [spinTranslation_mul, griessOctad_translation, griessOdd_translation,
    griessOdd_translation] at ht
  have hh := congrArg (fun v : SpinIndex =>
    v + griessOddOmegaCoefficient f j • Pi.single 11 1) ht
  have hr :
      (golayLabelCoefficients (golayOctadLabel o) +
        griessOctadOmegaCoefficient e • Pi.single 11 1) +
      (golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096) +
        griessOddOmegaCoefficient d i • Pi.single 11 1) +
        griessOddOmegaCoefficient f j • Pi.single 11 1 =
      (golayLabelCoefficients (golayOctadLabel o) +
        golayLabelCoefficients (⟨d.val, by omega⟩ : Fin 4096)) +
      (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
        griessOddOmegaCoefficient f j) • Pi.single 11 1 := by
    simp only [add_smul]
    abel
  rw [hr] at hh
  simpa only [add_assoc, ZModModule.add_self, add_zero] using hh.symm

/-- The actual octad/odd selector supplies the Parker theta addition law,
without assuming a low label for the octad or the intermediate sum. -/
theorem griessOctadOddQ_base_theta (o : Fin 759) (e : Fin 64)
    (d : Fin 2048) (i : Fin 24) (f : Fin 2048) (j : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base) :
    sourceWordTheta (⟨f.val, by omega⟩ : Fin 4096) =
      sourceWordTheta (golayOctadLabel o) +
        sourceWordTheta (⟨d.val, by omega⟩ : Fin 4096) +
      golaySyndrome (integerParity (sourceCodeIntersection (golayOctadLabel o)
        (⟨d.val, by omega⟩ : Fin 4096))) := by
  simp only [sourceWordTheta_polynomial]
  rw [griessOctadOddQ_base_translation o e d i f j hb,
    sourceCodeThetaPolynomial_add_smul_omega, sourceCodeThetaPolynomial_add]
  rw [sourceCodeIntersection_parity]

/-- Theta depends only on the dictionary code modulo the all-one generator. -/
theorem sourceCodeThetaPolynomial_dictionaryCode (t : SpinIndex) :
    sourceCodeThetaPolynomial t = sourceCodeThetaPolynomial
      (golayLabelCoefficients (⟨(spinDictionaryCode t).val, by omega⟩ : Fin 4096)) := by
  rcases spinDictionaryIndex_cases t with hlo | hhi
  · rw [hlo]
    simp only [spinDictionaryCode_low]
  · conv_lhs => rw [hhi, ← golayLabel_low_add_omega,
      sourceCodeThetaPolynomial_add_omega]

private theorem binary_three_cancel (a b c d : SpinIndex) (h : a + b + c = d) :
    a = b + d + c := by
  have hh := congrArg (fun x : SpinIndex => x + b + c) h
  have hr : (a + b + c) + b + c = a := by
    calc
      _ = a + (b + b) + (c + c) := by abel
      _ = a := by rw [ZModModule.add_self, ZModModule.add_self, add_zero, add_zero]
  rw [hr] at hh
  exact hh.trans (by abel)

/-- A dictionary selector also gives the theta identity in the reverse
code direction, with intersection against its actual input word. -/
theorem octadOdd_theta_of_selector (o : Fin 759) (d f : Fin 2048)
    (hs : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    sourceWordTheta (⟨f.val, by omega⟩ : Fin 4096) =
      sourceWordTheta (golayOctadLabel o) +
        sourceWordTheta (⟨d.val, by omega⟩ : Fin 4096) +
      golaySyndrome (integerParity (sourceCodeIntersection (golayOctadLabel o)
        (⟨f.val, by omega⟩ : Fin 4096))) := by
  have ht := sourceCodeThetaPolynomial_dictionaryCode (octadSpinLow f + octadSpinCode o)
  simp only [hs] at ht
  change sourceCodeThetaPolynomial (octadSpinLow f + octadSpinCode o) =
    sourceCodeThetaPolynomial (octadSpinLow d) at ht
  rw [sourceCodeThetaPolynomial_add] at ht
  have hp : (fun i => golayEncoder (octadSpinLow f) i *
      golayEncoder (octadSpinCode o) i) =
      integerParity (sourceCodeIntersection (golayOctadLabel o)
        (⟨f.val, by omega⟩ : Fin 4096)) := by
    rw [sourceCodeIntersection_parity]
    funext i
    exact mul_comm _ _
  rw [hp] at ht
  simp only [sourceWordTheta_polynomial]
  exact binary_three_cancel _ _ _ _ ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
