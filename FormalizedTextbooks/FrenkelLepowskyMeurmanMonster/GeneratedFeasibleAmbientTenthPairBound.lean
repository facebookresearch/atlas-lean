/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthFinalPairQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! Every pair row of the Tenth prototype has absolute value at most `3/32`. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The rational pair coefficient through the computable pair-coordinate table. -/
def generatedFeasibleAmbientTenthFinalPairQFast (s : Fin 2) (p : Fin 276) : ℚ :=
  (if s = 0 then 1 else -1) *
      generatedTenthIncomingMatrixQ (generatedAxisGlobalPairCoordinates p).1
        (generatedAxisGlobalPairCoordinates p).2 +
    ((generatedTenthIncomingPairNumerator 0 p : ℚ) -
      (generatedTenthIncomingPairNumerator 1 p : ℚ)) / 32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- All 552 pair coefficients are checked exactly.
private theorem pair_check : ∀ s : Fin 2, ∀ p : Fin 276,
    |generatedFeasibleAmbientTenthFinalPairQFast s p| ≤ 3 / 32 := by
  decide +kernel

/-- Every pair row of the Tenth prototype has absolute value at most `3/32`. -/
theorem generatedFeasibleAmbientTenth_pair_abs (s : Fin 2) (p : Fin 276) :
    |(griessConwayEncode generatedTenthAxis).2.1 (Sum.inl (s, p))| ≤ 3 / 32 := by
  rw [generatedTenth_final_pair_q]
  have he : generatedTenthFinalPairQ s p = generatedFeasibleAmbientTenthFinalPairQFast s p := by
    unfold generatedTenthFinalPairQ generatedFeasibleAmbientTenthFinalPairQFast
    rw [generatedAxisGlobalPairCoordinates_actual]
  rw [he]
  have h := pair_check s p
  have h' : ((|generatedFeasibleAmbientTenthFinalPairQFast s p| : ℚ) : ℝ) ≤ ((3 / 32 : ℚ) : ℝ) :=
      by exact_mod_cast h
  push_cast at h'
  exact h'

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
