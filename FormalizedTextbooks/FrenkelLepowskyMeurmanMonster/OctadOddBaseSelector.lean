/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual octad/odd preferred-Q base equality in physical code and Ω coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddQCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddTheta
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTensorFourier

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

noncomputable def octadOddIntersection (o : Fin 759) (f : Fin 2048) : Fin 24 → ZMod 2 :=
  fun k => golayOctadWord o k * golayEncoder (octadSpinLow f) k

/-- The actual intersection cocode in Parker addition is the physical octad restriction. -/
theorem octadOddIntersection_source (o : Fin 759) (f : Fin 2048) :
    integerParity (sourceCodeIntersection (golayOctadLabel o) ⟨f.val, by omega⟩) =
      octadOddIntersection o f := by
  rw [sourceCodeIntersection_parity]
  rfl

/-- Every actual octad/odd preferred-Q base equality has the source dictionary code selector. -/
theorem griessOctadOdd_base_code_selector (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hb : (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base) :
    spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d := by
  have ht := griessOctadOddQ_base_translation o e d i f j hb
  change octadSpinLow f = octadSpinCode o + octadSpinLow d +
    (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
      griessOddOmegaCoefficient f j) • Pi.single 11 1 at ht
  have hs : octadSpinLow f + octadSpinCode o = octadSpinLow d +
    (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
      griessOddOmegaCoefficient f j) • Pi.single 11 1 := by
    rw [ht]
    calc
      _ = octadSpinLow d +
        (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
          griessOddOmegaCoefficient f j) • Pi.single 11 1 +
          (octadSpinCode o+octadSpinCode o) := by abel
      _ = _ := by rw [ZModModule.add_self, add_zero]
  rw [hs]
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide +kernel)
    (griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
      griessOddOmegaCoefficient f j) with h | h
  · simp only [h, zero_smul, add_zero, octadSpinLow, spinDictionaryCode_low]
  · simp only [h, one_smul, spinDictionaryCode_add_omega,
      octadSpinLow, spinDictionaryCode_low]

/-- Under the actual dictionary code selector, the modulation condition is the physical syndrome. -/
theorem griessOctadOdd_modulation_physical (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    spinModulation (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))) =
        spinModulation (griessShortQ (Sum.inr (Sum.inr (f, j)))) ↔
      golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
        octadOddIntersection o f + Pi.single i 1 + Pi.single j 1) = 0 := by
  apply griessOctadOdd_modulation_selector
  rw [← octadOddIntersection_source]
  exact octadOdd_theta_of_selector o d f hd

/-- Exact preferred-Q output selection: actual code, physical syndrome and Ω parity. -/
theorem griessOctadOdd_base_iff_coordinates (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) :
    (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base ↔
    spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d ∧
      golaySyndrome (integerParity (griessOctadNegativeInteger o e) +
        octadOddIntersection o f + Pi.single i 1 + Pi.single j 1) = 0 ∧
      griessOctadOmegaCoefficient e + griessOddOmegaCoefficient d i +
        griessOddOmegaCoefficient f j + (octadSpinCode o) 11 = 0 := by
  constructor
  · intro hb
    have hd := griessOctadOdd_base_code_selector o e d f i j hb
    have hc := (qBase_eq_iff_spin_coordinates _ _).mp hb
    exact ⟨hd, (griessOctadOdd_modulation_physical o e d f i j hd).mp hc.2,
      (griessOctadOdd_translation_selector o e d f i j hd).mp hc.1⟩
  · rintro ⟨hd,hs,hω⟩
    apply (qBase_eq_iff_spin_coordinates _ _).mpr
    exact ⟨(griessOctadOdd_translation_selector o e d f i j hd).mpr hω,
      (griessOctadOdd_modulation_physical o e d f i j hd).mpr hs⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
