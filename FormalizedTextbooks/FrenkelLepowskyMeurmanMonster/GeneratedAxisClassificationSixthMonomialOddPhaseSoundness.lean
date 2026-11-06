/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddPhase

/-! Checked odd-phase data equals the entire actual preferred-Q phase at the genuine output. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The constant and coordinate cache retains every actual preferred-Q sign contribution. -/
theorem generatedSixth_monomial_odd_phase_cache (k : Fin 4) (r : GriessShortIndex)
    (f : Fin 512) (j : Fin 24)
    (hs : griessShortPermutation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.2 r =
      Sum.inr (Sum.inr (generatedSixthMonomialOddCode f, j))) :
    localShortPhase (generatedSixthCorrectedGenerator (Fin.castAdd 1 k)) r =
      generatedSixthMonomialOddPhase k f j := by
  rw [generatedSixth_monomial_odd_phase_at_output k r _ j hs,
    generatedSixth_monomial_mask_phase, generatedSixth_monomial_odd_phase_base]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
