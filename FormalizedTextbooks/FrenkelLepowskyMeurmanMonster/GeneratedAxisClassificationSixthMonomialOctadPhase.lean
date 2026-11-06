/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialShortPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisCharacters

/-! Signed octad transport retains the original quadratic and negative-coordinate data. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An Omega term never changes the original monomial quadratic phase. -/
theorem generatedSixth_monomial_phase_smul_omega (k : Fin 4) (t : SpinIndex) (c : ZMod 2) :
    monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
      (t + c • Pi.single 11 1) =
        monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase t := by
  rcases (show c = 0 ∨ c = 1 by exact (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c)
      with rfl | rfl
  · simp only [zero_smul, add_zero]
  · simpa only [one_smul] using generatedSixth_monomial_phase_add_omega k t

/-- Actual octad output determines the full phase without preferred-Q cache evaluation. -/
theorem generatedSixth_monomial_octad_phase_at_output (k : Fin 4)
    (r : GriessShortIndex) (o : Fin 759) (e : Fin 64)
    (hs : griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r =
      Sum.inr (Sum.inl (o, e))) :
    localShortPhase (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)) r =
      monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
        (golayLabelCoefficients (golayOctadLabel o)) +
      (spinDot (spinTranslation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)))
        (sourceWordTheta (golayOctadLabel o) +
          golaySyndrome (integerParity (griessOctadNegativeInteger o e))) +
      spinDot (spinModulation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)))
        (golayLabelCoefficients (golayOctadLabel o) +
          griessOctadOmegaCoefficient e • Pi.single 11 1)) := by
  rw [generatedSixth_monomial_short_phase_at_output k r _ hs,
    generatedFourthQShortBasis_character, griessOctad_translation, griessOctad_modulation,
    generatedSixth_monomial_phase_smul_omega]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
