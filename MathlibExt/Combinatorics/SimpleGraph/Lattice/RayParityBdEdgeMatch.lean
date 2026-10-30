/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchStarHull
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.MinimalPeriodLoop

/-!
# Ray parity determines the boundary of a set

If a closed lattice walk `Vc` has odd ray count exactly at the sites of `K`, then `K` is the inside
of `Vc` and the two sets have the same boundary edges (`pww_BdEdgeMatch K Vc`). The file checks
this for the unit cell `{(0, 0)}` and its face loop, which runs around the four faces at the
origin: the ray count of the loop is computed explicitly, the unit cell is closed under the
diagonal fill rules, and so it is its own star hull.

## Main results

* `StatMech.Lattice.jsf_bdEdgeMatch_of_rayParity`: odd ray count exactly on `K` gives
  `pww_BdEdgeMatch K Vc`.
* `StatMech.Lattice.jsf_unitCell_rayCount`: the ray count of the unit cell loop at every site.
* `StatMech.Lattice.jsf_unitCell_eq_leftRegion`: the unit cell is the inside of its loop.
* `StatMech.Lattice.jsf_starHull_unitCell_eq`: the unit cell is its own star hull.
* `StatMech.Lattice.jsf_starHull_bdEdgeMatch_of_rayParity`: the boundary-edge match for star hulls.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- If the closed walk `Vc` has odd ray count at every site of `K` and even ray count at every site
outside `K`, then `K` and the inside of `Vc` have the same boundary edges. -/
theorem jsf_bdEdgeMatch_of_rayParity {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
    pww_BdEdgeMatch K Vc :=
  pbs_bdEdgeMatch_of_leftRegion_eq Vc (ccs_cluster_eq_leftRegion Vc hin hout)

/-- The four edges of the face loop of the unit cell. -/
theorem jsf_unitCell_loop_edges :
    (mpl_orbitLoop unitCell ucBase).edges
      = [s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1]),
          s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0])] := by
  rw [mpl_orbitLoop_edges]; exact mpl_unitCell_faceLoop_edges

/-- The ray count of the unit cell loop at `z`: it counts the loop edges `(0, 0)–(0, -1)` and
`(-1, -1)–(-1, 0)` crossed by the ray of `z`. See also `StatMech.Lattice.eaw_unitCell_rayCount_eq`,
the same count written with other inequalities. -/
theorem jsf_unitCell_rayCount (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop unitCell ucBase)
      = (if z 1 = 0 ∧ 1 ≤ z 0 then 1 else 0)
        + (if z 1 = 0 ∧ 0 ≤ z 0 then 1 else 0) := by
  classical
  rw [jec_rayCount, jsf_unitCell_loop_edges]
  simp only [List.countP_cons, List.countP_nil]
  have h1 : decide (jec_rayEdge z s((![0, 0] : Site 2), ![0, -1]))
      = decide (z 1 = 0 ∧ 1 ≤ z 0) := by
    rw [decide_eq_decide]
    simp only [jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
    constructor
    · rintro ⟨h2, h3 | h4⟩ <;> omega
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  have h2 : decide (jec_rayEdge z s((![0, -1] : Site 2), ![-1, -1])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have h3 : decide (jec_rayEdge z s((![-1, -1] : Site 2), ![-1, 0]))
      = decide (z 1 = 0 ∧ 0 ≤ z 0) := by
    rw [decide_eq_decide]
    simp only [jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
    constructor
    · rintro ⟨h2, h3 | h4⟩ <;> omega
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  have h4 : decide (jec_rayEdge z s((![-1, 0] : Site 2), ![0, 0])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  rw [h1, h2, h3, h4]
  simp only [decide_eq_true_eq, Bool.false_eq_true, ite_false, add_zero, zero_add]
  exact Nat.add_comm _ _

/-- The origin has odd ray count with respect to the unit cell loop. -/
theorem jsf_unitCell_inside_odd (z : Site 2) (hz : z ∈ unitCell) :
    ¬ Even (jec_rayCount z (mpl_orbitLoop unitCell ucBase)) := by
  simp only [unitCell, Set.mem_singleton_iff] at hz
  subst hz
  rw [jsf_unitCell_rayCount]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Sites other than the origin have even ray count with respect to the unit cell loop. -/
theorem jsf_unitCell_outside_even (z : Site 2) (hz : z ∉ unitCell) :
    Even (jec_rayCount z (mpl_orbitLoop unitCell ucBase)) := by
  rw [jsf_unitCell_rayCount]
  have hne : ¬ (z 0 = 0 ∧ z 1 = 0) := by
    intro ⟨h0, h1⟩
    apply hz
    simp only [unitCell, Set.mem_singleton_iff]
    funext i; fin_cases i
    · simpa using h0
    · simpa using h1
  by_cases ha : z 1 = 0 ∧ 1 ≤ z 0 <;> by_cases hb : z 1 = 0 ∧ 0 ≤ z 0
  · simp only [ite_eq_left ha, ite_eq_left hb]; decide
  · simp only [ite_eq_left ha, ite_eq_right hb]; omega
  · exfalso
    obtain ⟨hb1, hb0⟩ := hb
    exact hne ⟨by omega, hb1⟩
  · simp only [ite_eq_right ha, ite_eq_right hb]; exact Even.zero

/-- The unit cell is the inside of its face loop. -/
theorem jsf_unitCell_eq_leftRegion :
    unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) :=
  ccs_cluster_eq_leftRegion (mpl_orbitLoop unitCell ucBase)
    jsf_unitCell_inside_odd jsf_unitCell_outside_even

/-- The unit cell and the inside of its face loop have the same boundary edges. -/
theorem jsf_unitCell_bdEdgeMatch :
    pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) :=
  jsf_bdEdgeMatch_of_rayParity (mpl_orbitLoop unitCell ucBase)
    jsf_unitCell_inside_odd jsf_unitCell_outside_even

/-- The unit cell is closed under the diagonal fill rules. -/
theorem jsf_unitCell_fillClosed : ndt_FillClosed unitCell := by
  refine ⟨fun f h00 h11 => ?_, fun f h10 h01 => ?_⟩
  · exfalso
    simp only [unitCell, Set.mem_singleton_iff, npd_P00, npd_P11] at h00 h11
    have e0 : f 0 = 0 := by have := congrFun h00 0; simpa using this
    have e1 : f 1 = 0 := by have := congrFun h00 1; simpa using this
    have := congrFun h11 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    omega
  · exfalso
    simp only [unitCell, Set.mem_singleton_iff, npd_P10, npd_P01] at h10 h01
    have e0 : f 0 + 1 = 0 := by have := congrFun h10 0; simpa using this
    have e1 : f 1 = 0 := by have := congrFun h10 1; simpa using this
    have := congrFun h01 0
    simp only [Matrix.cons_val_zero] at this
    omega

/-- The unit cell is its own star hull. -/
theorem jsf_starHull_unitCell_eq : ndt_StarHull unitCell = unitCell :=
  Set.Subset.antisymm
    (ndt_starHull_subset_of_fillClosed (le_refl _) jsf_unitCell_fillClosed)
    (ndt_subset_starHull _)

/-- The boundary-edge match for the star hull of the unit cell. -/
theorem jsf_starHull_unitCell_bdEdgeMatch :
    pww_BdEdgeMatch (ndt_StarHull unitCell) (mpl_orbitLoop unitCell ucBase) := by
  rw [jsf_starHull_unitCell_eq]; exact jsf_unitCell_bdEdgeMatch

/-- For a boundary orbit of a star hull, odd ray count exactly on the star hull gives the
boundary-edge match with the inside of its face loop. -/
theorem jsf_starHull_bdEdgeMatch_of_rayParity (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hin : ∀ z, z ∈ ndt_StarHull K →
      ¬ Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a)))
    (hout : ∀ z, z ∉ ndt_StarHull K →
      Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a))) :
    pww_BdEdgeMatch (ndt_StarHull K) (mpl_orbitLoop (ndt_StarHull K) a) :=
  jsf_bdEdgeMatch_of_rayParity (mpl_orbitLoop (ndt_StarHull K) a) hin hout

end Lattice

end StatMech
