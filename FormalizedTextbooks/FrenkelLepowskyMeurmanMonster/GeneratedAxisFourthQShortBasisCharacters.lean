/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQFixedCriteria
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.PairSpinDictionary
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine short-coordinate character is the literal translation-modulation pairing. -/
theorem generatedFourthQShortBasis_character (q : Q) (r : GriessShortIndex) :
    Multiplicative.toAdd (localAxisQPhase r q) =
      spinDot (spinTranslation q) (spinModulation (griessShortQ r)) +
        spinDot (spinModulation q) (spinTranslation (griessShortQ r)) := by
  have h (q k : Q) :
      Multiplicative.toAdd (localAxisBinaryPhase (Multiplicative.toAdd k.base) q) =
        spinDot (spinTranslation q) (spinModulation k) +
          spinDot (spinModulation q) (spinTranslation k) := by
    change qBeta (Multiplicative.toAdd q.base) (Multiplicative.toAdd k.base) +
      qBeta (Multiplicative.toAdd k.base) (Multiplicative.toAdd q.base) = _
    unfold qBeta spinDot spinTranslation spinModulation
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  exact h q (griessShortQ r)

/-- The signed-octad phase retains its Parker theta, negative signs and Omega contributions. -/
theorem generatedFourthQShortBasis_octad_character (u m : SpinIndex) (c : ZMod 2)
    (o : Fin 759) (e : Fin 64) :
    Multiplicative.toAdd (localAxisQPhase (Sum.inr (Sum.inl (o, e)))
      (generatedAxisFourthQFromSpin u m c)) =
      spinDot u (sourceWordTheta (golayOctadLabel o) +
        golaySyndrome (integerParity (griessOctadNegativeInteger o e))) +
      spinDot m (golayLabelCoefficients (golayOctadLabel o) +
        griessOctadOmegaCoefficient e • Pi.single 11 1) := by
  rw [generatedFourthQShortBasis_character, generatedAxisFourthQFromSpin_translation,
    generatedAxisFourthQFromSpin_modulation, griessOctad_modulation, griessOctad_translation]

/-- Vanishing of the literal binary pairing is exactly fixation of the actual short coordinate. -/
theorem generatedFourthQShortBasis_character_one_iff (q : Q) (r : GriessShortIndex) :
    localAxisQPhase r q = 1 ↔
      spinDot (spinTranslation q) (spinModulation (griessShortQ r)) +
        spinDot (spinModulation q) (spinTranslation (griessShortQ r)) = 0 := by
  rw [← generatedFourthQShortBasis_character]
  exact Multiplicative.toAdd.injective.eq_iff

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
