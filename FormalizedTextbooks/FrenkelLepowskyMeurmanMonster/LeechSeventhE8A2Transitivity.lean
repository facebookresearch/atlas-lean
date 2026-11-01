/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Orbit

/-! The original checked generator tree proves transitivity of the full actual section group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The initial plane of the genuine original-generator orbit tree. -/
def leechSeventhE8A2BasePlane : leechSeventhE8A2Planes :=
  leechSeventhE8A2PlaneEquiv (leechSeventhE8A2OrbitIndex 0)

/-- Every intrinsic actual A2 plane is reached from the initial plane in the full section group. -/
theorem leechSeventhE8A2BasePlane_reachable (W : leechSeventhE8A2Planes) :
    ∃ e : leechSeventhE8SectionGroup, e • leechSeventhE8A2BasePlane = W := by
  let p := leechSeventhE8A2PlaneEquiv.symm W
  obtain ⟨e, he⟩ := leechSeventhE8A2Orbit_reachable (leechSeventhE8A2OrbitInverse p)
  refine ⟨e, Subtype.ext ?_⟩
  change (leechSeventhE8A2Plane (leechSeventhE8A2OrbitIndex 0)).map
    e.val.val.toLinearMap = W.val
  rw [(leechSeventhE8A2_orbit_inverse p).2] at he
  exact he.trans (congrArg Subtype.val (leechSeventhE8A2PlaneEquiv.apply_symm_apply W))

/-- The full genuine section group acts transitively on its intrinsic actual A2 planes. -/
theorem leechSeventhE8A2Planes_transitive (W V : leechSeventhE8A2Planes) :
    ∃ e : leechSeventhE8SectionGroup, e • W = V := by
  obtain ⟨g, hg⟩ := leechSeventhE8A2BasePlane_reachable W
  obtain ⟨h, hh⟩ := leechSeventhE8A2BasePlane_reachable V
  refine ⟨h * g⁻¹, ?_⟩
  rw [← hg, mul_smul, inv_smul_smul, hh]

/-- Every actual section orbit is the entire intrinsic A2-plane carrier. -/
theorem leechSeventhE8A2Planes_action_orbit (W : leechSeventhE8A2Planes) :
    MulAction.orbit leechSeventhE8SectionGroup W = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro V
  exact leechSeventhE8A2Planes_transitive W V

/-- Every actual section orbit has exactly 1120 A2 planes. -/
theorem leechSeventhE8A2Planes_action_orbit_card (W : leechSeventhE8A2Planes) :
    Nat.card (MulAction.orbit leechSeventhE8SectionGroup W) = 1120 := by
  rw [leechSeventhE8A2Planes_action_orbit, Nat.card_univ, leechSeventhE8A2Planes_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
