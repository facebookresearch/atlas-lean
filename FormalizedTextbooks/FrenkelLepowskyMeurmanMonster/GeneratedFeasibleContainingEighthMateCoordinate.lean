/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthOrbitCount

/-! The actual preferred mate coefficient of the independently defined one-eighth destination. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original two preferred pair coefficients retain their exact sum through triality. -/
theorem generatedFeasibleContaining_triality_pair_coordinate_sum (x : GriessSpace) :
    (griessConwayEncode (sExtra x)).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) +
      (griessConwayEncode (sExtra x)).2.1 generatedFeasibleMateLabel =
        (griessConwayEncode x).2.1 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) -
          (griessConwayEncode x).2.1 generatedFeasibleMateLabel := by
  change (griessConwayEncode (sExtra x)).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) +
    (griessConwayEncode (sExtra x)).2.1
      (Sum.inl (1, generatedFeasiblePhysicalRootPair)) =
      (griessConwayEncode x).2.1 (Sum.inl (0, generatedFeasiblePhysicalRootPair)) -
        (griessConwayEncode x).2.1 (Sum.inl (1, generatedFeasiblePhysicalRootPair))
  rw [generatedFourthQShortBasis_triality_pair_minus,
    generatedFourthQShortBasis_triality_pair_plus]
  ring

/-- The genuine preferred mate, not merely its line, has coefficient seven eighths. -/
theorem generatedFeasibleContainingNewDestination_mate_coordinate :
    (griessConwayEncode generatedFeasibleContainingNewDestination).2.1
      generatedFeasibleMateLabel = 7 / 8 := by
  have h := generatedFeasibleContaining_triality_pair_coordinate_sum
    generatedFeasibleContainingNewIncoming
  change (griessConwayEncode generatedFeasibleContainingNewDestination).2.1
      (Sum.inl (0, generatedFeasiblePhysicalRootPair)) +
    (griessConwayEncode generatedFeasibleContainingNewDestination).2.1
      generatedFeasibleMateLabel = _ at h
  rw [generatedFeasibleContainingNewDestination_first_coordinate,
    generatedFeasibleContaining_first_coordinate _
      generatedFeasibleContainingNewIncoming_orbit,
    generatedFeasibleContainingNewIncoming_mate_zero] at h
  linarith

/-- Every entire vector in the genuine simultaneous orbit retains the preferred mate coefficient.
-/
theorem generatedFeasibleContainingEighth_N_orbit_mate_coordinate (x : GriessSpace)
    (hx : x ∈ generatedFeasibleContainingCoordinateNOrbit
      generatedFeasibleContainingNewDestination) :
    (griessConwayEncode x).2.1 generatedFeasibleMateLabel = 7 / 8 := by
  obtain ⟨n, rfl⟩ := hx
  rw [generatedFeasibleContaining_N_mate_coordinate,
    generatedFeasibleContainingNewDestination_mate_coordinate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
