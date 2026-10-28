/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSelectedOctadNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality

/-! Genuine outgoing selected octad coefficients include the entire original finite triality sum. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The complete integer triality sum for each selected outgoing original octad row. -/
def generatedTwelfthSelectedOctadNumerator (s : Fin 12) (e : Fin 64) : ℤ :=
  ∑ f : Fin 64, trialityIntegerMatrix e f * generatedTwelfthIncomingSelectedOctadNumerator s f

/-- Every selected outgoing original octad coefficient equals its entire checked packet sum. -/
theorem generatedTwelfth_selected_octad_numerator (s : Fin 12) (e : Fin 64) :
    (griessConwayEncode generatedTwelfthAxis).2.1
      (Sum.inr (Sum.inl (generatedTwelfthSelectedShortOctad s, e))) =
        (generatedTwelfthSelectedOctadNumerator s e : ℝ) / 128 := by
  rw [generatedTwelfthAxis_local_expression, generatedFourthQShortBasis_triality_octad]
  simp_rw [generatedTwelfth_incoming_selected_octad_numerator]
  rw [generatedTwelfthSelectedOctadNumerator]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro f _
  simp only [trialityRealMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  change ((1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ)) *
      ((generatedTwelfthIncomingSelectedOctadNumerator s f : ℝ) / 16) = _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
