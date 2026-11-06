/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual all-one correction in the literal source Y dictionary. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonActualCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Positive dictionary triality takes the full actual all-one lift to the central sign. -/
theorem monsterNortonSourceY_omega_conjugate :
    extraIntoGenerated * qIntoGenerated sourceOmegaQ * extraIntoGenerated⁻¹ =
      qIntoGenerated qCentralInvolution := by
  apply Subtype.ext
  change sExtra * rhoLocal (inclQ sourceOmegaQ) * sExtra⁻¹ =
    rhoLocal (inclQ qCentralInvolution)
  rw [sourceOmegaQ_eq_trialityCentralSign]
  change _ = localCentralGriess
  rw [localCentralGriess_eq_trialityCentralSign]
  simpa only [show trialityCycle 2 = 0 by decide] using trialityCentralSign_conjugate 2

/-- An exact source-code all-one decomposition gives the full literal Y central correction. -/
theorem monsterNortonSourceY_of_omega_decomposition (d b : Fin 4096) (h : ℕ)
    (hq : sourceQCode d 0 = sourceQCode b 0 * sourceOmegaQ ^ h) :
    y555NortonActualY d 0 =
      y555NortonActualY b 0 * (qIntoGenerated qCentralInvolution) ^ h := by
  rw [y555NortonActualY_word, y555NortonActualY_word]
  change extraIntoGenerated * qIntoGenerated (sourceQCode d 0) * extraIntoGenerated⁻¹ =
    (extraIntoGenerated * qIntoGenerated (sourceQCode b 0) * extraIntoGenerated⁻¹) *
      (qIntoGenerated qCentralInvolution) ^ h
  rw [hq, map_mul, map_pow, ← monsterNortonSourceY_omega_conjugate, conj_pow]
  group

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
