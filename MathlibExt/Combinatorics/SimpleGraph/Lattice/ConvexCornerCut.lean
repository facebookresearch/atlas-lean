/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EarContraction
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullPeriod

/-!
# Star hulls are nonempty; removing a convex corner can disconnect

The star hull of a nonempty set is nonempty. The rest of the file records an example about ear
removal: the four-site set `cutWitness = {(0,0), (1,0), (1,1), (2,1)}` is finite, nonempty and
king-saturated (so its boundary face loops are cycles), and its lexicographically extreme site
`(1, 1)` is a convex corner of the boundary (the turn there is `-1`), yet removing that site
leaves a set that is not connected in the square lattice. So "remove an extreme convex corner"
does not preserve connectivity, even for king-saturated sets with simple boundary cycles.

## Main results

* `StatMech.Lattice.sht_starHull_nonempty`: the star hull of a nonempty set is nonempty.
* `StatMech.Lattice.sht_cutWitness_kingSaturated`: `cutWitness` is king-saturated.
* `StatMech.Lattice.sht_kingSat_singleCycle_convex_corner_can_disconnect`: some finite,
  nonempty, king-saturated set has an extreme convex corner whose removal disconnects it.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The star hull of a nonempty set is nonempty. -/
theorem sht_starHull_nonempty (K : Set (Site 2)) (hne : K.Nonempty) : (ndt_StarHull K).Nonempty :=
  hne.mono (ndt_subset_starHull K)

/-- Two vectors `![a, b]` and `![c, d]` of `ℤ²` are equal iff their coordinates are. See also
`Matrix.vecCons_inj`. -/
theorem sht_vec2_eq (a b c d : ℤ) : (![a, b] : Site 2) = ![c, d] ↔ a = c ∧ b = d := by
  rw [funext_iff, Fin.forall_fin_two]; simp

/-- The set `cutWitness` is king-saturated: whenever it contains two opposite corners of a face it
contains a third corner. -/
theorem sht_cutWitness_kingSaturated : npm_KingSaturated cutWitness := by
  intro f
  have hP00 : npd_P00 f = ![f 0, f 1] := rfl
  have hP10 : npd_P10 f = ![f 0 + 1, f 1] := rfl
  have hP11 : npd_P11 f = ![f 0 + 1, f 1 + 1] := rfl
  have hP01 : npd_P01 f = ![f 0, f 1 + 1] := rfl
  simp only [mem_cutWitness, hP00, hP10, hP11, hP01, sht_vec2_eq]
  omega

/-- The set `cutWitness` is finite. -/
theorem sht_cutWitness_finite : cutWitness.Finite := by
  unfold cutWitness; exact Set.toFinite _

/-- The set `cutWitness` is nonempty. -/
theorem sht_cutWitness_nonempty : cutWitness.Nonempty := ⟨_, cw_v00⟩

/-- The face loop of every boundary orbit of `cutWitness` is a cycle. -/
theorem sht_cutWitness_orbit_isCycle (a : {e : Dart // IsBoundaryDart cutWitness e}) :
    ((dartOrbitFaceWalk cutWitness a.1 a.2 (dartOrbitPeriod cutWitness a)).copy rfl
      (by rw [orbit_iterate_period_eq cutWitness a])).IsCycle :=
  emb_orbit_isCycle_of_kingSaturated cutWitness a
    (shp_period_ge_three cutWitness sht_cutWitness_finite a) sht_cutWitness_kingSaturated

/-- Removing an extreme convex corner can disconnect a set: there are a finite, nonempty,
king-saturated set `K` and an extreme site `c` of `K` at which the boundary turns clockwise
(`turnZ K (leftDart c) = -1`) such that `K \ {c}` is not connected in the square lattice.
The example is `cutWitness` with `c = (1, 1)`. -/
theorem sht_kingSat_singleCycle_convex_corner_can_disconnect :
    ∃ (K : Set (Site 2)) (c : Site 2),
      K.Finite ∧ K.Nonempty ∧ npm_KingSaturated K ∧ IsExtremeCell K c ∧
      turnZ K (leftDart c) = -1 ∧ ¬ CellConnected (K \ {c}) :=
  ⟨cutWitness, ![1, 1], sht_cutWitness_finite, sht_cutWitness_nonempty,
    sht_cutWitness_kingSaturated, cutWitness_extreme,
    extremeCell_turnZ cutWitness ![1, 1] cutWitness_extreme,
    cutWitness_diff_not_cellConnected⟩

end Lattice

end StatMech
