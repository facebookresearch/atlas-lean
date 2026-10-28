/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactTensorSign
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthFullQProjectionTransfer

/-! Replacing the complete incoming source by a compatible compact fiber preserves
the actual final root-eight local orbit and the projections of attained fixers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Equal whole-Q incoming actions have final triality images connected by an actual
local element with trivial Conway projection. No spin-scalar calibration is required. -/
theorem generatedRootEight_incoming_central_projection_orbit (f : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation (generatedTenthQWordFiber 8).val.1) :
    ∃ u : H, projH u = 1 ∧ generatedFifthRootEightAxis =
      rhoLocal u (sExtra (rhoLocal (localFiberIntoH f) generatedFifthAxis)) := by
  have ht := generatedTwelfth_full_Q_triality_projection_orbit
    (generatedTenthQWordFiber 8) f he.symm generatedFifthAxis
  rw [generatedTenth_Q_word_fiber_local] at ht
  rw [generatedFifthRootEightAxis_local_expression]
  exact ht

/-- The compact final triality destination belongs to precisely the actual root-eight H orbit. -/
theorem generatedRootEight_incoming_central_orbit_transport (f : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation (generatedTenthQWordFiber 8).val.1) :
    ∃ u : H, generatedFifthRootEightAxis =
      rhoLocal u (sExtra (rhoLocal (localFiberIntoH f) generatedFifthAxis)) := by
  obtain ⟨u, _, hu⟩ := generatedRootEight_incoming_central_projection_orbit f he
  exact ⟨u, hu⟩

/-- A full compact final-axis fixer supplies an actual root-eight fixer with the same
Conway projection. Fixation of the complete Griess vector remains an explicit premise. -/
theorem generatedRootEight_incoming_central_fixer_transfer (f : localFiberSubgroup)
    (he : spinConjugation f.val.1 = spinConjugation (generatedTenthQWordFiber 8).val.1)
    (h : H) (hfix : rhoLocal h (sExtra (rhoLocal (localFiberIntoH f) generatedFifthAxis)) =
      sExtra (rhoLocal (localFiberIntoH f) generatedFifthAxis)) :
    ∃ k : H, projH k = projH h ∧
      rhoLocal k generatedFifthRootEightAxis = generatedFifthRootEightAxis := by
  have ht := generatedTwelfth_full_Q_triality_fixer_transfer
    (generatedTenthQWordFiber 8) f he.symm generatedFifthAxis h hfix
  rw [generatedTenth_Q_word_fiber_local] at ht
  rw [generatedFifthRootEightAxis_local_expression]
  exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
