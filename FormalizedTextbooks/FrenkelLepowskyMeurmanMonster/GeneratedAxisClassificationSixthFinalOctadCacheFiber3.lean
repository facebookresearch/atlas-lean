/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheData

/-! Bounded exact finite fibers of the original middle-octad code map. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check original code equality and membership in the at most three displayed rows.
/-- All original rows with the displayed code are exactly the listed one or three rows. -/
theorem generatedSixth_final_octad_cache_fiber3 (j : Fin 33) :
    Finset.univ.filter (fun r : Fin 273 => generatedSixthMiddleOctadCode r =
      generatedSixthFinalOctadCacheCode ⟨3 * 33 + j.val, by omega⟩) =
        generatedSixthFinalOctadCacheRows ⟨3 * 33 + j.val, by omega⟩ := by
  have h : ∀ j : Fin 33, ∀ r : Fin 273,
      generatedSixthMiddleOctadCode r =
        generatedSixthFinalOctadCacheCode ⟨3 * 33 + j.val, by omega⟩ ↔
      r ∈ generatedSixthFinalOctadCacheRows ⟨3 * 33 + j.val, by omega⟩ := by
    decide +kernel
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h j r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
