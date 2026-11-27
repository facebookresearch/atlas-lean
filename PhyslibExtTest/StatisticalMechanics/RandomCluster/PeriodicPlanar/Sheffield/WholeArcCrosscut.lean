/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.WholeArcCrosscut

/-!
# Tests for `Sheffield.WholeArcCrosscut`

Module under test: `Sheffield.WholeArcCrosscut` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

On `ℤ²`, the crosscut `(0,0) – (0,1) – (0,2)` on the line `x = 0` and the escape walk
`(0,1) – (1,1)`:
* `StatMech.Lattice.halfPlane_walks_intersect` applies (`α = 0`, `β = 1`);
* `StatMech.Lattice.halfPlane_walks_intersect_of_endpoint_outside` applies via its first
  disjunct;
* `PeriodicPlanarDualPair.no_open_primal_dual_of_wholeArcBoundaryIncidence` elaborates
  (check-only; no concrete planar dual pair is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace WholeArcCrosscut

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice SimpleGraph

/-- The crosscut `(0,0) – (0,1) – (0,2)`. -/
def crosscut : (hypercubicLattice 2).Walk ![0, 0] ![0, 2] :=
  .cons (v := ![0, 1]) (by simp [Fin.sum_univ_two])
    (.cons (by simp [Fin.sum_univ_two]) .nil)

/-- The escape walk `(0,1) – (1,1)`. -/
def escape : (hypercubicLattice 2).Walk ![0, 1] ![1, 1] :=
  .cons (by simp [Fin.sum_univ_two]) .nil

/-- Every vertex of the crosscut has first coordinate `0`. -/
theorem crosscut_support (z : Site 2) (hz : z ∈ crosscut.support) : z 0 = 0 := by
  simp only [crosscut, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl <;> rfl

/-- Every vertex of the escape walk has nonnegative first coordinate. -/
theorem escape_support (z : Site 2) (hz : z ∈ escape.support) : 0 ≤ z 0 := by
  simp only [escape, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl <;> simp

-- The crosscut and the escape walk meet.
example : ∃ z, z ∈ crosscut.support ∧ z ∈ escape.support :=
  halfPlane_walks_intersect 0 0 2 1 1 1 (by norm_num) (by norm_num) crosscut escape
    (fun z hz => (crosscut_support z hz).ge) (fun z hz => by rw [crosscut_support z hz]; norm_num)
    escape_support

-- The same through the endpoint-outside form (the escape ends to the right of the crosscut).
example : ∃ z, z ∈ crosscut.support ∧ z ∈ escape.support :=
  halfPlane_walks_intersect_of_endpoint_outside 0 0 2 1 1 1 (by norm_num) (by norm_num) crosscut
    escape (fun z hz => (crosscut_support z hz).ge) escape_support
    (Or.inl fun z hz => by rw [crosscut_support z hz]; norm_num)

-- `PeriodicPlanarDualPair.no_open_primal_dual_of_wholeArcBoundaryIncidence` elaborates.
example := @PeriodicPlanarDualPair.no_open_primal_dual_of_wholeArcBoundaryIncidence

end WholeArcCrosscut
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
