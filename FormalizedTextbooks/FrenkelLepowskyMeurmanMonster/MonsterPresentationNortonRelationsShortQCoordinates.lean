/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite source-coordinate evaluation of every genuine preferred short-Q label. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The source code translation, including the genuine preferred-lift Ω correction. -/
def monsterNortonShortTranslation : GriessShortIndex → SpinIndex
  | Sum.inl (s, _) => if s = 0 then 0 else Pi.single 11 1
  | Sum.inr (Sum.inl (d, e)) => golayLabelCoefficients (golayOctadLabel d) +
      griessOctadOmegaCoefficient e • Pi.single 11 1
  | Sum.inr (Sum.inr (d, j)) => golayLabelCoefficients ⟨d.val, by omega⟩ +
      griessOddOmegaCoefficient d j • Pi.single 11 1

/-- The source cocode character of the genuine preferred short lift. -/
def monsterNortonShortModulation : GriessShortIndex → SpinIndex
  | Sum.inl (_, p) => griessPairSyndrome p
  | Sum.inr (Sum.inl (d, e)) => sourceWordTheta (golayOctadLabel d) +
      golaySyndrome (integerParity (griessOctadNegativeInteger d e))
  | Sum.inr (Sum.inr (d, j)) => sourceWordTheta ⟨d.val, by omega⟩ +
      (fun k => (golayGeneratorBit k j : ZMod 2))

/-- These source translations equal the intrinsic actual Q translations on all three families. -/
theorem monsterNortonShortTranslation_actual (r : GriessShortIndex) :
    spinTranslation (griessShortQ r) = monsterNortonShortTranslation r := by
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · fin_cases s
    · exact griessPairMinus_translation p
    · exact griessPairPlus_translation p
  · exact griessOctad_translation d e
  · exact griessOdd_translation d j

/-- These source characters equal the intrinsic actual Q modulations on all three families. -/
theorem monsterNortonShortModulation_actual (r : GriessShortIndex) :
    spinModulation (griessShortQ r) = monsterNortonShortModulation r := by
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · fin_cases s
    · exact griessPairMinus_modulation p
    · exact griessPairPlus_modulation p
  · exact griessOctad_modulation d e
  · exact griessOdd_modulation d j

/-- A finite preferred-Q evaluator using the already proved full source dictionary. -/
def monsterNortonShortQSource (r : GriessShortIndex) : Q :=
  ⟨ofAdd (Fin.append (monsterNortonShortTranslation r) (monsterNortonShortModulation r)), 1⟩

/-- The source evaluator is exactly the actual preferred lift, with its central coefficient. -/
theorem monsterNortonShortQSource_actual (r : GriessShortIndex) :
    monsterNortonShortQSource r = griessShortQ r := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change Fin.append (monsterNortonShortTranslation r)
      (monsterNortonShortModulation r) = toAdd (griessShortQ r).base
    funext i
    refine Fin.addCases (m := 12) (n := 12) (fun k => ?_) (fun k => ?_) i
    · rw [Fin.append_left]
      change monsterNortonShortTranslation r k = spinTranslation (griessShortQ r) k
      exact congrFun (monsterNortonShortTranslation_actual r).symm k
    · rw [Fin.append_right]
      change monsterNortonShortModulation r k = spinModulation (griessShortQ r) k
      exact congrFun (monsterNortonShortModulation_actual r).symm k
  · rfl

/-- The source evaluator also equals the certified integer-coordinate evaluator. -/
theorem monsterNortonShortQSource_eq (r : GriessShortIndex) :
    monsterNortonShortQSource r = monsterNortonShortQ r := by
  rw [monsterNortonShortQSource_actual, monsterNortonShortQ_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
