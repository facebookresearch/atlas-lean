/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7XiCorrectionActions

/-! Complete source-coordinate identification for the correcting E7 move. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option maxRecDepth 100000

/-- Twice the standard-octad E7 projector perpendicular to e4+e5. -/
def generatedTenthE7XiProjection : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  (if i = j ∧ i.val < 8 then 2 else 0) -
    (if i = 4 ∨ i = 5 then 1 else 0) * (if j = 4 ∨ j = 5 then 1 else 0)

/-- The complete corrected matrix commutes with the entire E7 projector. -/
theorem generatedTenth_e7_xi_projection_commute_integer :
    generatedTenthE7XiCorrectedNumerator * generatedTenthE7XiProjection =
      generatedTenthE7XiProjection * generatedTenthE7XiCorrectedNumerator := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Bind all 576 projector entries to the complete original five-letter Golay word.
/-- The genuine source word carries the standard E7 projector to the actual one. -/
theorem generatedTenth_e7_xi_projection_transport : ∀ i j : Fin 24,
    generatedTenthE7XiProjection i j = generatedTenthE7ProjectionInteger
      (generatedTenthE8StandardPermutation.val i) (generatedTenthE8StandardPermutation.val j) := by
  unfold generatedTenthE7ProjectionInteger generatedTenthE7XiProjection
  decide +kernel

/-- The complete source word carries both fixed vectors to their actual original coordinates. -/
theorem generatedTenth_e7_xi_vectors_transport :
    golayIntegerPermute generatedTenthE8StandardPermutation.val generatedTenthE7XiLine =
        generatedTenthE7DistinguishedVector ∧
      golayIntegerPermute generatedTenthE8StandardPermutation.val generatedTenthE7XiNormal =
        generatedTenthE7NormalVector := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
