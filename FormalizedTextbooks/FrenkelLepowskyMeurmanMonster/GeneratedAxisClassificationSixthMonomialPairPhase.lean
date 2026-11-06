/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialShortPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialMaskData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignPair

/-! The complete original preferred pair phase reduces to its two genuine Golay code signs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual Q correction has exactly its displayed original code translation. -/
theorem generatedSixth_monomial_correction_translation (k : Fin 4) :
    spinTranslation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) =
      golayLabelCoefficients (generatedSixthMonomialMaskTranslation k) := by
  fin_cases k <;> exact generatedAxisFourthQFromSpin_translation _ _ _

/-- Actual pair output has zero raw quadratic phase, including the plus-pair Omega term. -/
theorem generatedSixth_monomial_raw_pair_phase_zero (k : Fin 4) (s : Fin 2) (p : Fin 276) :
    monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
      (spinTranslation (griessShortQ (Sum.inl (s, p)))) = 0 := by
  rw [griessPairQ_translation]
  split_ifs
  · simp [monsterMonomialQuadratic]
  · have h := generatedSixth_monomial_phase_add_omega k 0
    simpa [monsterMonomialQuadratic] using h

/-- Once genuine pair output is bound, all preferred signs are the two original code bits. -/
theorem generatedSixth_monomial_pair_phase_at_output (k : Fin 4) (r : GriessShortIndex)
    (s : Fin 2) (p : Fin 276)
    (hs : griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r =
      Sum.inl (s, p)) :
    localShortPhase (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)) r =
      golayEncoder (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k))
        (griessCoordinatePair p).1 +
      golayEncoder (golayLabelCoefficients (generatedSixthMonomialMaskTranslation k))
        (griessCoordinatePair p).2 := by
  rw [generatedSixth_monomial_short_phase_at_output k r _ hs,
    generatedSixth_monomial_raw_pair_phase_zero, zero_add,
    ← localAxisQPhase_eq_short_phase]
  apply generatedFifth_sign_Q_pair_phase
  · exact generatedSixth_monomial_correction_translation k
  · have h := generatedSixth_monomial_correction_even k
    simpa [spinDot, Pi.single_apply] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
