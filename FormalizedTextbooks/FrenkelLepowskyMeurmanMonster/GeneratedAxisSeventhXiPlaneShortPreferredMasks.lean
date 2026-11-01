/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortSyndromeMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary

/-! Genuine pair, octad and odd preferred lifts evaluated by their complete source masks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem zero_coeff : golayLabelCoefficients (0 : Fin 4096) = 0 := by
  funext k
  simp [golayLabelCoefficients]

private theorem omega_coeff : golayLabelCoefficients (2048 : Fin 4096) =
    Pi.single (11 : Fin 12) 1 := by decide +kernel

/-- The original source omega correction is kept in the translation mask. -/
def generatedSeventhXiShortTranslationMask (d : Fin 4096) (c : ZMod 2) : Fin 4096 :=
  monsterNortonBitXor d (if c = 0 then 0 else 2048)

/-- The translation mask preserves every source omega coefficient. -/
theorem generatedSeventhXiShortTranslationMask_actual (d : Fin 4096) (c : ZMod 2) :
    golayLabelCoefficients (generatedSeventhXiShortTranslationMask d c) =
      golayLabelCoefficients d + c • Pi.single 11 1 := by
  rw [generatedSeventhXiShortTranslationMask, monsterNortonBitXor_coeff]
  by_cases hc : c = 0
  · subst c
    simp only [ite_true, zero_coeff, zero_smul, add_zero]
  · have h1 : c = 1 := by revert c; decide +kernel
    rw [ite_eq_right hc, omega_coeff, h1, one_smul]

/-- The modulation mask keeps both original Parker theta and the actual physical syndrome. -/
def generatedSeventhXiShortModulationMask (d : Fin 4096) (v : ℕ) : Fin 4096 :=
  monsterNortonBitXor (generatedSeventhXiShortThetaSplit d)
    (generatedSeventhXiShortSyndromeMask v)

/-- Every original theta and selected physical syndrome bit is retained. -/
theorem generatedSeventhXiShortModulationMask_actual (d : Fin 4096) (v : ℕ) :
    golayLabelCoefficients (generatedSeventhXiShortModulationMask d v) =
      sourceWordTheta d + golaySyndrome (fun i => golayBooleanCast (v.testBit i.val)) := by
  rw [generatedSeventhXiShortModulationMask, monsterNortonBitXor_coeff,
    ← generatedSeventhXiShortThetaSplit_actual, generatedSeventhXiShortSyndromeMask_actual]

/-- Every signed-octad preferred lift has the full source translation and modulation masks. -/
theorem generatedSeventhXiShortOctadMask_actual (o : Fin 759) (e : Fin 64) :
    griessShortQ (Sum.inr (Sum.inl (o, e))) =
      generatedSeventhXiShortQMask (generatedSeventhXiShortQJoinMask
        (generatedSeventhXiShortTranslationMask (golayOctadLabel o)
          (griessOctadOmegaCoefficient e))
        (generatedSeventhXiShortModulationMask (golayOctadLabel o) (griessOctadSignMask o e))) := by
  apply generatedSeventhXiShortQMask_preferred
  · rw [generatedSeventhXiShortTranslationMask_actual, griessOctad_translation]
  · have hn : integerParity (griessOctadNegativeInteger o e) =
        (fun i => golayBooleanCast ((griessOctadSignMask o e).testBit i.val)) := by
      funext i
      cases h : (griessOctadSignMask o e).testBit i.val <;>
        simp [integerParity, griessOctadNegativeInteger, h, golayBooleanCast]
    rw [generatedSeventhXiShortModulationMask_actual, griessOctad_modulation, hn]

/-- Odd preferred lifts retain the actual source theta and the distinguished physical column. -/
theorem generatedSeventhXiShortOddMask_actual (d : Fin 2048) (j : Fin 24) :
    griessShortQ (Sum.inr (Sum.inr (d, j))) =
      generatedSeventhXiShortQMask (generatedSeventhXiShortQJoinMask
        (generatedSeventhXiShortTranslationMask ⟨d.val, by omega⟩ (griessOddOmegaCoefficient d j))
        (monsterNortonBitXor (generatedSeventhXiShortThetaSplit ⟨d.val, by omega⟩)
          (generatedSeventhXiShortCocodeColumn j))) := by
  apply generatedSeventhXiShortQMask_preferred
  · rw [generatedSeventhXiShortTranslationMask_actual, griessOdd_translation]
  · rw [monsterNortonBitXor_coeff, ← generatedSeventhXiShortThetaSplit_actual,
      griessOdd_modulation, generatedSeventhXiShortCocodeColumn_actual]

/-- Both preferred pair phases share the actual two-coordinate cocode syndrome. -/
theorem generatedSeventhXiShortPairMask_actual (s : Fin 2) (p : Fin 276) :
    griessShortQ (Sum.inl (s, p)) =
      generatedSeventhXiShortQMask (generatedSeventhXiShortQJoinMask
        (if s = 0 then 0 else 2048)
        (monsterNortonBitXor (generatedSeventhXiShortCocodeColumn (griessCoordinatePair p).1)
          (generatedSeventhXiShortCocodeColumn (griessCoordinatePair p).2))) := by
  apply generatedSeventhXiShortQMask_preferred
  · fin_cases s
    · change spinTranslation (griessShortQ (Sum.inl (0, p))) = golayLabelCoefficients 0
      rw [griessPairMinus_translation, zero_coeff]
    · change spinTranslation (griessShortQ (Sum.inl (1, p))) = golayLabelCoefficients 2048
      rw [griessPairPlus_translation, omega_coeff]
  · have hm : spinModulation (griessShortQ (Sum.inl (s, p))) = griessPairSyndrome p := by
      fin_cases s
      · change spinModulation (griessShortQ (Sum.inl (0, p))) = _
        exact griessPairMinus_modulation p
      · change spinModulation (griessShortQ (Sum.inl (1, p))) = _
        exact griessPairPlus_modulation p
    rw [hm, monsterNortonBitXor_coeff, generatedSeventhXiShortCocodeColumn_actual,
      generatedSeventhXiShortCocodeColumn_actual]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
