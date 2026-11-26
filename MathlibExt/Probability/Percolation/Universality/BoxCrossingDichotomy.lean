/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.RSW.Defs
public import MathlibExt.Probability.Percolation.RSW.SelfDuality

/-!
# The left-reach set of a square and the separation half of the crossing dichotomy

For a bond configuration `ω` on `ℤ²` and the square `rect 0 n 0 n`, the *left-reach set* is the
set of sites of the square joined to its left side by an open path inside the square. There is no
open left–right crossing exactly when the left-reach set misses the right side. In that case the
left-reach set is a finite set containing the left side and missing the right side, and every
lattice edge inside the square from the left-reach set to its complement is closed. This is the
primal half of the argument for the box-crossing dichotomy (an open horizontal crossing of a
rectangle, or a closed vertical crossing of the dual rectangle, but not both).

This file does **not** prove the dichotomy: it stops at the closed edge boundary. Turning that
boundary into a closed top–bottom dual crossing needs a planar-dual path argument that is not
formalized here; `MathlibExt.Probability.Percolation.Universality.FaceDualDichotomy` only obtains
a face-boundary cycle around the left-reach set.

## Main definitions

* `StatMech.Universality.bcd_leftReach`: the sites of `rect 0 n 0 n` joined to the left side by an
  open path inside the square.

## Main results

* `StatMech.Universality.bcd_horizontal_iff_right_in_leftReach`: an open horizontal crossing
  exists iff some right-side site lies in the left-reach set.
* `StatMech.Universality.bcd_leftReach_boundary_closed`: an in-square edge leaving the left-reach
  set is closed.
* `StatMech.Universality.bcd_separation`: without a horizontal crossing, the left-reach set is
  finite, contains the left side, misses the right side, and has closed in-square edge boundary.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, Ch. 11.
* B. Bollobás and O. Riordan, *Percolation*, Cambridge University Press, 2006, Ch. 3.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}

/-- The left-reach set of the square `rect 0 n 0 n`: the sites of the square joined to some site
of the left side by an `ω`-open path that stays inside the square. -/
def bcd_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Set (Site 2) :=
  {v | v ∈ rect 0 n 0 n ∧ ∃ (x : Site 2) (hx : x ∈ leftSide 0 n 0 n) (hv : v ∈ rect 0 n 0 n),
      ConnectedWithin 2 ω (rect 0 n 0 n) ⟨x, leftSide_subset hx⟩ ⟨v, hv⟩}

theorem bcd_leftReach_subset_box (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    bcd_leftReach ω n ⊆ rect 0 n 0 n := fun _ hv => hv.1

/-- An open left–right crossing of the square exists iff the left-reach set meets the right
side. -/
theorem bcd_horizontal_iff_right_in_leftReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    HorizontalCrossing ω 0 n 0 n ↔
      ∃ y : Site 2, y ∈ rightSide 0 n 0 n ∧ y ∈ bcd_leftReach ω n := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨y, y.2, rightSide_subset y.2, ?_⟩
    exact ⟨x, x.2, rightSide_subset y.2, hxy⟩
  · rintro ⟨y, hyR, _hybox, x, hxL, hyb, hconn⟩
    exact ⟨⟨x, hxL⟩, ⟨y, hyR⟩, hconn⟩

/-- There is no open left–right crossing iff no right-side site lies in the left-reach set. -/
theorem bcd_no_horizontal_iff_right_unreachable (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    ¬ HorizontalCrossing ω 0 n 0 n ↔
      ∀ y : Site 2, y ∈ rightSide 0 n 0 n → y ∉ bcd_leftReach ω n := by
  rw [bcd_horizontal_iff_right_in_leftReach]
  push Not
  rfl

/-- The left-reach set is closed under open lattice steps inside the square. -/
theorem bcd_leftReach_extend (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hopen : ω s(v, w) = true) :
    w ∈ bcd_leftReach ω n := by
  obtain ⟨hvbox, x, hxL, hvbox', hconn⟩ := hv
  refine ⟨hwbox, x, hxL, hwbox, ?_⟩
  have hstep : (openSubgraphInduce 2 ω (rect 0 n 0 n)).Adj ⟨v, hvbox'⟩ ⟨w, hwbox⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hconn.trans hstep.reachable

/-- A lattice edge inside the square from the left-reach set to its complement is closed. -/
theorem bcd_leftReach_boundary_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcd_leftReach ω n) :
    ω s(v, w) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact hw (bcd_leftReach_extend ω n hv hwbox hadj h)

/-- The rotated image `crossEdge s(v, w)` of an edge leaving the left-reach set is open in the
rotated dual configuration `dualConfig ω`. Note that `crossEdge` is the quarter-turn rotation,
not the geometric dual edge (see `crossEdge`). -/
theorem bcd_leftReach_boundary_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcd_leftReach ω n) :
    dualConfig ω (crossEdge s(v, w)) = true := by
  rw [StatMech.RSW.dualCross_open_iff_closed]
  exact bcd_leftReach_boundary_closed ω n hv hwbox hadj hw

theorem bcd_leftReach_finite (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (bcd_leftReach ω n).Finite :=
  (rect_finite 0 n 0 n).subset (bcd_leftReach_subset_box ω n)

/-- Without an open horizontal crossing, the left-reach set misses the right side. -/
theorem bcd_leftReach_disjoint_rightSide (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    Disjoint (bcd_leftReach ω n) (rightSide 0 n 0 n) := by
  rw [Set.disjoint_right]
  intro y hyR hyL
  exact (bcd_no_horizontal_iff_right_unreachable ω n).mp hnoH y hyR hyL

/-- **Separation half of the box-crossing dichotomy.** If `rect 0 n 0 n` has no open left–right
crossing, its left-reach set is finite, contains the left side, misses the right side, and every
in-square lattice edge leaving it is closed (so its rotated image is open in `dualConfig ω`).

This is only the primal separation step. It does not produce a dual crossing; compare the full
dichotomy in Grimmett, *Percolation*, 2nd ed., 1999, Ch. 11, and Bollobás–Riordan, *Percolation*,
2006, Ch. 3. -/
theorem bcd_separation (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ x ∈ leftSide 0 n 0 n, x ∈ bcd_leftReach ω n) ∧
      Disjoint (bcd_leftReach ω n) (rightSide 0 n 0 n) ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        ω s(v, w) = false ∧ dualConfig ω (crossEdge s(v, w)) = true) := by
  refine ⟨bcd_leftReach_finite ω n, ?_, bcd_leftReach_disjoint_rightSide ω n hnoH, ?_⟩
  · intro x hx
    refine ⟨leftSide_subset hx, x, hx, leftSide_subset hx, ?_⟩
    exact connectedWithin_refl ω (rect 0 n 0 n) ⟨x, leftSide_subset hx⟩
  · intro v w hv hwbox hadj hw
    exact ⟨bcd_leftReach_boundary_closed ω n hv hwbox hadj hw,
      bcd_leftReach_boundary_dual_open ω n hv hwbox hadj hw⟩

end Universality

end StatMech
