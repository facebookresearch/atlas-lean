/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairQFinite

/-! Executable full original preferred-Q lifts for every actual short dictionary coordinate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Negative positions evaluated through the checked original octad coordinate catalogue. -/
def generatedAxisGlobalOctadNegativeInteger (j : Fin 759) (e : Fin 64) (i : Fin 24) : ℤ :=
  if ((List.finRange 8).foldr (fun (k : Fin 8) (m : ℕ) =>
      (if (trialityEvenMask e).testBit k.val then
        2 ^ (generatedAxisGlobalOctadCoordinatesData j k).val else 0) ||| m) 0).testBit i.val
    then 1 else 0

/-- The finite negative-position formula is the intrinsic actual octad vector. -/
theorem generatedAxisGlobalOctadNegativeInteger_actual (j : Fin 759) (e : Fin 64) :
    generatedAxisGlobalOctadNegativeInteger j e = griessOctadNegativeInteger j e := by
  funext i
  unfold generatedAxisGlobalOctadNegativeInteger griessOctadNegativeInteger griessOctadSignMask
  simp_rw [generatedAxisGlobalOctadCoordinatesData_actual]

/-- The complete preferred lift, including every code, cocode, and Ω correction. -/
def generatedAxisGlobalShortQFinite : GriessShortIndex → Q
  | Sum.inl (s, p) => generatedAxisGlobalPairQFinite s p
  | Sum.inr (Sum.inl (j, e)) =>
      ⟨ofAdd (Fin.append
        (golayLabelCoefficients (generatedAxisGlobalOctadCodeData j) +
          griessOctadOmegaCoefficient e • Pi.single 11 1)
        (sourceWordTheta (generatedAxisGlobalOctadCodeData j) +
          golaySyndrome (integerParity (generatedAxisGlobalOctadNegativeInteger j e)))), 1⟩
  | Sum.inr (Sum.inr p) => monsterNortonShortQSource (Sum.inr (Sum.inr p))

/-- Every finite formula is the entire actual preferred-Q element of its short coordinate. -/
theorem generatedAxisGlobalShortQFinite_actual (r : GriessShortIndex) :
    generatedAxisGlobalShortQFinite r = griessShortQ r := by
  rcases r with ⟨s, p⟩ | (⟨j, e⟩ | p)
  · exact generatedAxisGlobalPairQFinite_actual s p
  · rw [← monsterNortonShortQSource_actual]
    simp only [generatedAxisGlobalShortQFinite, monsterNortonShortQSource,
      monsterNortonShortTranslation, monsterNortonShortModulation]
    rw [generatedAxisGlobalOctadCodeData_actual, generatedAxisGlobalOctadNegativeInteger_actual]
  · exact monsterNortonShortQSource_actual (Sum.inr (Sum.inr p))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
