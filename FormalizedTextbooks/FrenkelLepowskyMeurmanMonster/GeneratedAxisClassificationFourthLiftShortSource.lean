/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortQCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenRootLabels

/-! Original preferred-Q coordinates for all signs in the actual fourth octad families. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original even negative-position mask at the recorded genuine octad coordinates. -/
def generatedFourthLiftShortSignMask (j : Fin 63) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedFourthEvenRootCoordinates j k).val else 0) ||| m) 0

/-- The finite mask is the actual preferred sign mask for every sign index. -/
theorem generatedFourth_lift_short_sign_mask (j : Fin 63) (e : Fin 64) :
    griessOctadSignMask (generatedFourthEvenRootOctad j) e =
      generatedFourthLiftShortSignMask j e := by
  simp only [griessOctadSignMask, generatedFourth_even_coordinates_certificate,
    generatedFourthLiftShortSignMask]

/-- A finite source evaluator retains both the actual Omega correction and Parker theta. -/
def generatedFourthLiftShortSourceQ (j : Fin 63) (e : Fin 64) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients (generatedFourthEvenRootCode j) +
      griessOctadOmegaCoefficient e • Pi.single 11 1)
    (sourceWordTheta (generatedFourthEvenRootCode j) +
      golaySyndrome (integerParity (fun i : Fin 24 =>
        if (generatedFourthLiftShortSignMask j e).testBit i.val then (1 : ℤ) else 0)))), 1⟩

/-- The finite evaluator is the genuine preferred lift in the actual short catalogue. -/
theorem generatedFourth_lift_short_source_q (j : Fin 63) (e : Fin 64) :
    generatedFourthLiftShortSourceQ j e =
      griessShortQ (Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e))) := by
  have hn : griessOctadNegativeInteger (generatedFourthEvenRootOctad j) e =
      (fun i : Fin 24 =>
        if (generatedFourthLiftShortSignMask j e).testBit i.val then (1 : ℤ) else 0) := by
    funext i
    rw [griessOctadNegativeInteger, generatedFourth_lift_short_sign_mask]
  rw [← monsterNortonShortQSource_actual]
  simp only [monsterNortonShortQSource, monsterNortonShortTranslation,
    monsterNortonShortModulation, generatedFourthEvenRootOctad_label,
    hn, generatedFourthLiftShortSourceQ]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
