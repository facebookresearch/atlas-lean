/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitGroup

/-! Genuine actual matrix-fixing words attain every complete original E7 root address. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original root class is attained by a genuine member of the entire actual matrix group. -/
theorem generatedTenth_e7_root_orbit_positive_reachable (n : Fin 63) :
    ∃ g : generatedTenthE7PositiveRootMatrixGroup,
      leechModTwoAction g.val.val (generatedTenthE7OrbitNodeClass 0) =
        generatedTenthE7OrbitNodeClass n := by
  generalize he : n.val = r
  induction r using Nat.strong_induction_on generalizing n with
  | h r ih =>
    by_cases hz : n = 0
    · subst n
      refine ⟨1, ?_⟩
      change leechModTwoAction 1 _ = _
      rw [map_one]
      rfl
    · have hlt : (generatedTenthE7OrbitParent n).val < r := by
        rw [← he]
        exact generatedTenth_e7_orbit_parent_lt n hz
      obtain ⟨g, hg⟩ := ih _ hlt (generatedTenthE7OrbitParent n) rfl
      refine ⟨generatedTenthE7RootOrbitPositiveLetter (generatedTenthE7OrbitLetter n) * g, ?_⟩
      change leechModTwoAction
        (generatedTenthE7OrbitSpatialLetter (generatedTenthE7OrbitLetter n) * g.val.val) _ = _
      rw [map_mul]
      change leechModTwoAction (generatedTenthE7OrbitSpatialLetter (generatedTenthE7OrbitLetter n))
        (leechModTwoAction g.val.val (generatedTenthE7OrbitNodeClass 0)) = _
      rw [hg]
      exact generatedTenth_e7_orbit_edge_class n (generatedTenth_e7_orbit_edges_actual n hz)

/-- Every actual root address is reached by an actual original matrix fixer. -/
theorem generatedTenth_e7_root_orbit_reachable (n : Fin 63) :
    ∃ g : generatedTenthE7StandardMatrixGroup,
      leechModTwoAction g.val (generatedTenthE7OrbitNodeClass 0) =
        generatedTenthE7OrbitNodeClass n := by
  obtain ⟨g, hg⟩ := generatedTenth_e7_root_orbit_positive_reachable n
  exact ⟨g.val, hg⟩

/-- Every pair in the entire actual sixty-three-root catalogue is joined by a genuine
original matrix-fixing isometry, expressed in standard root coordinates. -/
theorem generatedTenth_e7_root_orbit_between (i j : Fin 63) :
    ∃ g : generatedTenthE7StandardMatrixGroup,
      leechModTwoAction g.val (generatedTenthE7OrbitNodeClass i) =
        generatedTenthE7OrbitNodeClass j := by
  obtain ⟨a, ha⟩ := generatedTenth_e7_root_orbit_reachable i
  obtain ⟨b, hb⟩ := generatedTenth_e7_root_orbit_reachable j
  refine ⟨b * a⁻¹, ?_⟩
  change leechModTwoAction (b.val * a.val⁻¹) _ = _
  rw [map_mul, map_inv, ← ha]
  change leechModTwoAction b.val
    ((leechModTwoAction a.val).symm
      (leechModTwoAction a.val (generatedTenthE7OrbitNodeClass 0))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact hb

/-- Every pair is joined by an actual matrix fixer retaining the positive normal root. -/
theorem generatedTenth_e7_root_orbit_positive_between (i j : Fin 63) :
    ∃ g : generatedTenthE7StandardMatrixGroup,
      leechIntegralAction g.val generatedTenthE7OrbitNormalRoot = generatedTenthE7OrbitNormalRoot ∧
        leechModTwoAction g.val (generatedTenthE7OrbitNodeClass i) =
          generatedTenthE7OrbitNodeClass j := by
  obtain ⟨a, ha⟩ := generatedTenth_e7_root_orbit_positive_reachable i
  obtain ⟨b, hb⟩ := generatedTenth_e7_root_orbit_positive_reachable j
  let g : generatedTenthE7PositiveRootMatrixGroup := b * a⁻¹
  refine ⟨g.val, g.property, ?_⟩
  change leechModTwoAction (b.val.val * a.val.val⁻¹) _ = _
  rw [map_mul, map_inv, ← ha]
  change leechModTwoAction b.val.val
    ((leechModTwoAction a.val.val).symm
      (leechModTwoAction a.val.val (generatedTenthE7OrbitNodeClass 0))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact hb

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
