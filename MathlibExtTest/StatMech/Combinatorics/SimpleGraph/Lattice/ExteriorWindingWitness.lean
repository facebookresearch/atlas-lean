/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness`

* `exc_OffSupportReachesExterior` holds for the unit cell: its face loop visits `(0, 0)`,
  `(0, -1)`, `(-1, -1)` and `(-1, 0)`, and every other site of the box `[-1, 1]²` has a
  neighbour outside the box.
* With `exc_unitCell_supportOddInK`, the three results apply to the unit cell: the inside of its
  loop is the unit cell, and its orbit has a winding witness.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness

/-- The face loop of the unit cell orbit visits `(0, 0)`, `(0, -1)`, `(-1, -1)` and `(-1, 0)`. -/
theorem unitCell_orbitLoop_support :
    (mpl_orbitLoop unitCell ucBase).support
      = [![0, 0], ![0, -1], ![-1, -1], ![-1, 0], ![0, 0]] := by
  rw [mpl_orbitLoop_support, mpl_orbitFaceLoop, SimpleGraph.Walk.support_copy,
    dartOrbitFaceWalk_support, unitCell_orbitPeriod_eq_four]
  change [dartFace ((dartNext unitCell)^[0] ucDart0), dartFace ((dartNext unitCell)^[1] ucDart0),
      dartFace ((dartNext unitCell)^[2] ucDart0), dartFace ((dartNext unitCell)^[3] ucDart0),
      dartFace ((dartNext unitCell)^[4] ucDart0)] = _
  rw [mpl_dartFace_iterate_ucDart0, mpl_dartFace_iterate_ucDart1, mpl_dartFace_iterate_ucDart2,
    mpl_dartFace_iterate_ucDart3, mpl_dartFace_iterate_ucDart4]

/-- Every site outside the unit cell and off its face loop is joined, avoiding the loop, to a site
outside the box `[-1, 1]²`: the site itself if it lies outside the box, and otherwise its right
neighbour (first coordinate `1`) or its upper neighbour (second coordinate `1`). -/
theorem unitCell_offSupportReachesExterior : exc_OffSupportReachesExterior unitCell ucBase := by
  have hsupp (z : Site 2) : z ∈ (mpl_orbitLoop unitCell ucBase).support ↔
      z = ![0, 0] ∨ z = ![0, -1] ∨ z = ![-1, -1] ∨ z = ![-1, 0] := by
    rw [unitCell_orbitLoop_support]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  refine ⟨1, ?_, ?_⟩
  · intro z hz
    replace hz : z ∈ (mpl_orbitLoop unitCell ucBase).support := hz
    rw [hsupp] at hz
    rw [mem_box]
    intro i
    rcases hz with rfl | rfl | rfl | rfl <;> fin_cases i <;> decide
  · intro z _ hz
    refine ⟨hz, ?_⟩
    by_cases hext : z ∈ exterior 2 1
    · exact ⟨z, hext, SimpleGraph.Reachable.refl _⟩
    have hbox (i : Fin 2) : (z i).natAbs ≤ 1 := by
      by_contra h
      exact hext ⟨i, by omega⟩
    have hz0 := hbox 0
    have hz1 := hbox 1
    have hone : z 0 = 1 ∨ z 1 = 1 := by
      by_contra hne
      push Not at hne
      apply hz
      rw [hsupp]
      have hx : z 0 = 0 ∨ z 0 = -1 := by omega
      have hy : z 1 = 0 ∨ z 1 = -1 := by omega
      have hzeq : z = ![z 0, z 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hzeq]
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]
    rcases hone with h0 | h1
    · refine ⟨![2, z 1], ⟨0, by simp⟩, SimpleGraph.Adj.reachable ?_⟩
      change (hypercubicLattice 2).Adj z ![2, z 1]
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [h0]
    · refine ⟨![z 0, 2], ⟨1, by simp⟩, SimpleGraph.Adj.reachable ?_⟩
      change (hypercubicLattice 2).Adj z ![z 0, 2]
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp [h1]

/-- The inside of the unit cell loop is the unit cell: it is contained in the unit cell by
`ecd_leftRegion_subset_of_exc`, and the origin has ray count `1`. -/
example : jec_leftRegion (mpl_orbitLoop unitCell ucBase) = unitCell := by
  refine Set.Subset.antisymm (ecd_leftRegion_subset_of_exc unitCell ucBase
    unitCell_offSupportReachesExterior exc_unitCell_supportOddInK) ?_
  intro z hz
  rw [unitCell, Set.mem_singleton_iff] at hz
  rw [hz, jec_mem_leftRegion, mpl_unitCell_rayCount_eq_one]
  decide

/-- The unit cell orbit has a winding witness. -/
example : wei_WindingWitness unitCell ucBase :=
  ecd_windingWitness_of_cycle_exc unitCell ucBase
    (by rw [unitCell_orbitPeriod_eq_four]; norm_num) usc_unitCell_noPinch
    unitCell_offSupportReachesExterior exc_unitCell_supportOddInK

/-- The three conjuncts of `eaw_LoopWindsRegion` for the unit cell orbit. -/
example : 3 ≤ dartOrbitPeriod unitCell ucBase ∧ OrbitFaceNoPinch unitCell ucBase ∧
    eaw_InteriorSubset unitCell ucBase :=
  ecd_loopWindsRegion_conjuncts_of_exc unitCell ucBase
    (by rw [unitCell_orbitPeriod_eq_four]; norm_num) usc_unitCell_noPinch
    unitCell_offSupportReachesExterior exc_unitCell_supportOddInK

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness
