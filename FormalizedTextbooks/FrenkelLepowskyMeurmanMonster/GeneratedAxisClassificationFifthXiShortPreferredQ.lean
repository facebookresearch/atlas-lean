/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthShortOctadQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortVectorQTransport

/-! Actual preferred Q lifts for the pair and octad rows in the fifth-axis short support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine even short labels, comprising the actual pair and signed-octad rows. -/
abbrev generatedFifthXiEvenShortLabel := (Fin 2 × Fin 276) ⊕ (Fin 759 × Fin 64)

/-- Embed these even labels into the actual preferred-short coordinate dictionary. -/
def generatedFifthXiEvenShortIndex : generatedFifthXiEvenShortLabel → GriessShortIndex
  | Sum.inl p => Sum.inl p
  | Sum.inr o => Sum.inr (Sum.inl o)

/-- A preferred even-short Q lift given by its genuine translation and modulation formulas. -/
def generatedFifthXiEvenShortQ : generatedFifthXiEvenShortLabel → Q
  | Sum.inl (s, p) => generatedAxisFourthQFromSpin
      (if s = 0 then 0 else Pi.single 11 1) (griessPairSyndrome p) 0
  | Sum.inr (o, e) => generatedAxisFourthQFromSpin
      (golayLabelCoefficients (golayOctadLabel o) +
        griessOctadOmegaCoefficient e • Pi.single 11 1)
      (sourceWordTheta (golayOctadLabel o) +
        golaySyndrome (integerParity (griessOctadNegativeInteger o e))) 0

/-- These explicit formulas are the actual preferred Q lifts, with central coefficient zero. -/
theorem generatedFifthXiEvenShortQ_actual (r : generatedFifthXiEvenShortLabel) :
    generatedFifthXiEvenShortQ r = griessShortQ (generatedFifthXiEvenShortIndex r) := by
  rcases r with ⟨s, p⟩ | ⟨o, e⟩
  · apply generatedAxisFourthQ_spin_coordinates_injective
    · exact (generatedAxisFourthQFromSpin_translation _ _ _).trans
        (griessPairQ_translation s p).symm
    · exact (generatedAxisFourthQFromSpin_modulation _ _ _).trans
        (griessPairQ_modulation s p).symm
    · exact (generatedAxisFourthQFromSpin_coeff _ _ _).trans
        (griessShortQ_coeff _).symm
  · apply generatedAxisFourthQ_spin_coordinates_injective
    · exact (generatedAxisFourthQFromSpin_translation _ _ _).trans
        (griessOctad_translation o e).symm
    · exact (generatedAxisFourthQFromSpin_modulation _ _ _).trans
        (griessOctad_modulation o e).symm
    · exact (generatedAxisFourthQFromSpin_coeff _ _ _).trans
        (griessShortQ_coeff _).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
