/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CellEulerBound
import Code.Onsager.InsideConnected
import Code.Onsager.JedBridge
import Code.Lattice.JordanClusterBridge

namespace StatMech.Onsager.WalkCellRegion

open Finset SimpleGraph Set
open StatMech.Lattice
open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.InsideConnected StatMech.Onsager.JedBridge


def cellFace : (ℤ × ℤ) ≃ Site 2 where
  toFun p := ![p.1, p.2]
  invFun z := (z 0, z 1)
  left_inv p := by ext <;> rfl
  right_inv z := by funext i; fin_cases i <;> rfl

@[simp] theorem cellFace_zero (p : ℤ × ℤ) : cellFace p 0 = p.1 := rfl
@[simp] theorem cellFace_one (p : ℤ × ℤ) : cellFace p 1 = p.2 := rfl
@[simp] theorem cellFace_symm (z : Site 2) : cellFace.symm z = (z 0, z 1) := rfl

section Walk

variable {m : ℕ}

noncomputable abbrev walkP (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    PlanarZ2Subgraph := walkSubgraph d hclosed hsimple

noncomputable abbrev walkRegionGraph (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d)) :
    SimpleGraph (Site 2) := whb_faceRegion (imageGraph (walkP d hclosed hsimple))


theorem walkEdge_mem_imageGraph (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (k : Fin (m + 3)) :
    s(posSite d k, posSite d (k + 1)) ∈ (imageGraph (walkP d hclosed hsimple)).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  refine ⟨k, k + 1, ?_, rfl, rfl⟩
  change (cycleGraph (m + 3)).Adj k (k + 1)
  rw [cycleGraph_adj]
  right
  simp



theorem imageGraph_adj_pos_iff (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (k : Fin (m + 3)) (q : Site 2) :
    (imageGraph (walkP d hclosed hsimple)).Adj (posSite d k) q ↔
      q = posSite d (k - 1) ∨ q = posSite d (k + 1) := by
  constructor
  · change (∃ i j : Fin (m + 3), (cycleGraph (m + 3)).Adj i j ∧
      posSite d i = posSite d k ∧ posSite d j = q) → _
    rintro ⟨i, j, hij, hi, hj⟩
    have hik : i = k := posSite_injective d hsimple hi
    subst i
    rw [cycleGraph_adj] at hij
    rcases hij with hij | hij
    · left
      rw [← hj]
      congr 1
      have hjk : j + 1 = k := by
        simpa [add_comm] using (sub_eq_iff_eq_add.mp hij).symm
      exact eq_sub_of_add_eq hjk
    · right
      rw [← hj]
      congr 1
      simpa [add_comm] using sub_eq_iff_eq_add.mp hij
  · rintro (rfl | rfl)
    · rw [imageGraph_adj]
      refine ⟨k, k - 1, ?_, rfl, rfl⟩
      change (cycleGraph (m + 3)).Adj k (k - 1)
      rw [cycleGraph_adj]
      left
      simp
    · rw [← SimpleGraph.mem_edgeSet]
      exact walkEdge_mem_imageGraph d hclosed hsimple k


theorem rayParity_eq_of_faceAdj_right (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (a b : ℤ)
    (hadj : (walkRegionGraph d hclosed hsimple).Adj (cellFace (a, b))
      (cellFace (a + 1, b))) :
    rayParity d a b = rayParity d (a + 1) b := by
  apply rayParity_hstep d hclosed a b
  intro k hk hcol hspan
  have hx := vert_x_const d hclosed k hk
  have hy := vert_y_step d hclosed k hk
  have hedge : s(posSite d k, posSite d (k + 1)) =
      sharedPrimalEdge (cellFace (a, b)) (cellFace (a + 1, b)) := by
    change s(posSite d k, posSite d (k + 1)) = sharedPrimalEdge ![a, b] ![a + 1, b]
    rw [sharedPrimalEdge_right]
    unfold faceCorner10 faceCorner11
    have hk0 : posSite d k = ![a + 1, (pos d k).2] := by
      funext i; fin_cases i <;> simp [posSite, hcol]
    rcases hy with hy | hy
    · have hk1 : posSite d (k + 1) = ![a + 1, (pos d k).2 + 1] := by
        funext i; fin_cases i <;> simp [posSite, hx, hcol, hy]
      rw [hk0, hk1, Sym2.eq_iff]
      left
      constructor <;> funext i <;> fin_cases i <;> simp <;> omega
    · have hk1 : posSite d (k + 1) = ![a + 1, (pos d k).2 - 1] := by
        funext i; fin_cases i <;> simp [posSite, hx, hcol, hy]
      rw [hk0, hk1, Sym2.eq_iff]
      right
      constructor <;> funext i <;> fin_cases i <;> simp <;> omega
  rw [whb_faceRegion_adj] at hadj
  exact hadj.2 (hedge ▸ walkEdge_mem_imageGraph d hclosed hsimple k)


theorem rayParity_eq_of_faceAdj_top (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (a b : ℤ)
    (hadj : (walkRegionGraph d hclosed hsimple).Adj (cellFace (a, b))
      (cellFace (a, b + 1))) :
    rayParity d a b = rayParity d a (b + 1) := by
  apply rayParity_vstep d a b
  intro k hk hcol hheight
  have hy := horiz_y_const d hclosed k hk
  have hx := horiz_x_step d hclosed k hk
  have hedge : s(posSite d k, posSite d (k + 1)) =
      sharedPrimalEdge (cellFace (a, b)) (cellFace (a, b + 1)) := by
    change s(posSite d k, posSite d (k + 1)) = sharedPrimalEdge ![a, b] ![a, b + 1]
    rw [sharedPrimalEdge_top]
    unfold faceCorner01 faceCorner11
    have hk0 : posSite d k = ![(pos d k).1, b + 1] := by
      funext i; fin_cases i <;> simp [posSite, hheight]
    rcases hx with hx | hx
    · have hk1 : posSite d (k + 1) = ![(pos d k).1 + 1, b + 1] := by
        funext i; fin_cases i <;> simp [posSite, hx, hy, hheight]
      rw [hk0, hk1, Sym2.eq_iff]
      left
      constructor <;> funext i <;> fin_cases i <;> simp <;> omega
    · have hk1 : posSite d (k + 1) = ![(pos d k).1 - 1, b + 1] := by
        funext i; fin_cases i <;> simp [posSite, hx, hy, hheight]
      rw [hk0, hk1, Sym2.eq_iff]
      right
      constructor <;> funext i <;> fin_cases i <;> simp <;> omega
  rw [whb_faceRegion_adj] at hadj
  exact hadj.2 (hedge ▸ walkEdge_mem_imageGraph d hclosed hsimple k)


theorem rayParity_eq_of_faceAdj (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    {f g : Site 2} (hadj : (walkRegionGraph d hclosed hsimple).Adj f g) :
    rayParity d (f 0) (f 1) = rayParity d (g 0) (g 1) := by
  have hlat := hadj.1
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  by_cases hx : f 0 = g 0
  · have hy : f 1 = g 1 + 1 ∨ g 1 = f 1 + 1 := by
      have : (f 1 - g 1).natAbs = 1 := by omega
      rcases Int.natAbs_eq_iff.mp this with h | h <;> omega
    rcases hy with hy | hy
    · have hadj' : (walkRegionGraph d hclosed hsimple).Adj
          (cellFace (g 0, g 1)) (cellFace (g 0, g 1 + 1)) := by
        convert hadj.symm using 1 <;> funext i <;> fin_cases i <;> simp_all
      simpa [hx, hy] using
        (rayParity_eq_of_faceAdj_top d hclosed hsimple (g 0) (g 1) hadj').symm
    · have hadj' : (walkRegionGraph d hclosed hsimple).Adj
          (cellFace (f 0, f 1)) (cellFace (f 0, f 1 + 1)) := by
        convert hadj using 1 <;> funext i <;> fin_cases i <;> simp_all
      simpa [hx, hy] using rayParity_eq_of_faceAdj_top d hclosed hsimple (f 0) (f 1) hadj'
  · have hy : f 1 = g 1 := by omega
    have hx' : f 0 = g 0 + 1 ∨ g 0 = f 0 + 1 := by
      have : (f 0 - g 0).natAbs = 1 := by omega
      rcases Int.natAbs_eq_iff.mp this with h | h <;> omega
    rcases hx' with hx' | hx'
    · have hadj' : (walkRegionGraph d hclosed hsimple).Adj
          (cellFace (g 0, g 1)) (cellFace (g 0 + 1, g 1)) := by
        convert hadj.symm using 1 <;> funext i <;> fin_cases i <;> simp_all
      simpa [hy, hx'] using
        (rayParity_eq_of_faceAdj_right d hclosed hsimple (g 0) (g 1) hadj').symm
    · have hadj' : (walkRegionGraph d hclosed hsimple).Adj
          (cellFace (f 0, f 1)) (cellFace (f 0 + 1, f 1)) := by
        convert hadj using 1 <;> funext i <;> fin_cases i <;> simp_all
      simpa [hy, hx'] using rayParity_eq_of_faceAdj_right d hclosed hsimple (f 0) (f 1) hadj'


theorem rayParity_eq_of_reachable (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    {f g : Site 2} (hreach : (walkRegionGraph d hclosed hsimple).Reachable f g) :
    rayParity d (f 0) (f 1) = rayParity d (g 0) (g 1) := by
  obtain ⟨w⟩ := hreach
  induction w with
  | nil => rfl
  | cons h p ih => exact (rayParity_eq_of_faceAdj d hclosed hsimple h).trans ih

variable (d : Fin (m + 3) → Fin 4)
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)


noncomputable def lexInteriorIndex : Fin (m + 3) :=
  (lexmax_corner_cell_inside d hclosed hsimple hreflexfree).choose

theorem lexInteriorIndex_spec :
    d (lexInteriorIndex d hclosed hsimple hreflexfree - 1) = 1 ∧
      d (lexInteriorIndex d hclosed hsimple hreflexfree) = 2 ∧
      rayParity d
        ((pos d (lexInteriorIndex d hclosed hsimple hreflexfree)).1 - 1)
        ((pos d (lexInteriorIndex d hclosed hsimple hreflexfree)).2 - 1) = 1 :=
  (lexmax_corner_cell_inside d hclosed hsimple hreflexfree).choose_spec


noncomputable def lexInteriorFace : Site 2 :=
  cellFace
    ((pos d (lexInteriorIndex d hclosed hsimple hreflexfree)).1 - 1,
      (pos d (lexInteriorIndex d hclosed hsimple hreflexfree)).2 - 1)

theorem lexInteriorFace_parity :
    rayParity d (lexInteriorFace d hclosed hsimple hreflexfree 0)
      (lexInteriorFace d hclosed hsimple hreflexfree 1) = 1 := by
  exact (lexInteriorIndex_spec d hclosed hsimple hreflexfree).2.2


noncomputable def innerComponent :
    (walkRegionGraph d hclosed hsimple).ConnectedComponent :=
  (walkRegionGraph d hclosed hsimple).connectedComponentMk
    (lexInteriorFace d hclosed hsimple hreflexfree)


theorem outerBeacon_parity :
    rayParity d
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 0)
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1) 1) = 0 := by
  apply rayParity_topOutside d _ _ (outerBoxRadius (walkP d hclosed hsimple))
  · intro j
    have hj := outerBoxRadius_spec (walkP d hclosed hsimple) j
    rw [mem_box] at hj
    have hj1 := hj 1
    change (pos d j).2.natAbs ≤ outerBoxRadius (walkP d hclosed hsimple) at hj1
    omega
  · change (outerBoxRadius (walkP d hclosed hsimple) : ℤ) ≤
      (outerBoxRadius (walkP d hclosed hsimple) : ℤ) + 1 + 1
    omega


theorem innerComponent_finite :
    (innerComponent d hclosed hsimple hreflexfree).supp.Finite := by
  apply (jfc_whb_bounded_iff_ne_outer (walkP d hclosed hsimple)
    (innerComponent d hclosed hsimple hreflexfree)).2
  intro heq
  have hcomp :
      (walkRegionGraph d hclosed hsimple).connectedComponentMk
          (lexInteriorFace d hclosed hsimple hreflexfree) =
        (walkRegionGraph d hclosed hsimple).connectedComponentMk
          (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := by
    exact heq
  have hreach : (walkRegionGraph d hclosed hsimple).Reachable
      (lexInteriorFace d hclosed hsimple hreflexfree)
      (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) :=
    ConnectedComponent.eq.mp hcomp
  have hp := rayParity_eq_of_reachable d hclosed hsimple hreach
  rw [lexInteriorFace_parity d hclosed hsimple hreflexfree,
    outerBeacon_parity d hclosed hsimple] at hp
  exact one_ne_zero hp


def componentCellSet : Set (ℤ × ℤ) :=
  {p | cellFace p ∈ (innerComponent d hclosed hsimple hreflexfree).supp}

theorem componentCellSet_finite :
    (componentCellSet d hclosed hsimple hreflexfree).Finite := by
  exact (innerComponent_finite d hclosed hsimple hreflexfree).preimage
    cellFace.injective.injOn

noncomputable def interiorCells : Finset (ℤ × ℤ) :=
  (componentCellSet_finite d hclosed hsimple hreflexfree).toFinset

@[simp] theorem mem_interiorCells (p : ℤ × ℤ) :
    p ∈ interiorCells d hclosed hsimple hreflexfree ↔
      cellFace p ∈ (innerComponent d hclosed hsimple hreflexfree).supp := by
  rw [interiorCells, Set.Finite.mem_toFinset]
  rfl


theorem mem_interiorCells_iff_rayParity (p : ℤ × ℤ) :
    p ∈ interiorCells d hclosed hsimple hreflexfree ↔ rayParity d p.1 p.2 = 1 := by
  constructor
  · intro hp
    rw [mem_interiorCells] at hp
    have hcomp := (innerComponent d hclosed hsimple hreflexfree).mem_supp_iff (cellFace p) |>.mp hp
    have hreach : (walkRegionGraph d hclosed hsimple).Reachable
        (cellFace p) (lexInteriorFace d hclosed hsimple hreflexfree) := by
      rw [← ConnectedComponent.eq]
      exact hcomp.trans (by rfl)
    have hpar := rayParity_eq_of_reachable d hclosed hsimple hreach
    simpa [lexInteriorFace_parity d hclosed hsimple hreflexfree] using hpar
  · intro hp
    let C := (walkRegionGraph d hclosed hsimple).connectedComponentMk (cellFace p)
    have hCne : C ≠ jfc_whb_outerRegion (walkP d hclosed hsimple) := by
      intro hEq
      have hcomp : (walkRegionGraph d hclosed hsimple).connectedComponentMk (cellFace p) =
          (walkRegionGraph d hclosed hsimple).connectedComponentMk
            (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) := hEq
      have hreach : (walkRegionGraph d hclosed hsimple).Reachable (cellFace p)
          (beacon 2 (outerBoxRadius (walkP d hclosed hsimple) + 1)) :=
        ConnectedComponent.eq.mp hcomp
      have hpar := rayParity_eq_of_reachable d hclosed hsimple hreach
      change rayParity d p.1 p.2 = _ at hpar
      rw [hp, outerBeacon_parity d hclosed hsimple] at hpar
      exact one_ne_zero hpar
    have hCfin : C.supp.Finite :=
      (jfc_whb_bounded_iff_ne_outer (walkP d hclosed hsimple) C).2 hCne
    let inner : jcb_BoundedRegion (walkP d hclosed hsimple) :=
      ⟨innerComponent d hclosed hsimple hreflexfree,
        innerComponent_finite d hclosed hsimple hreflexfree⟩
    let current : jcb_BoundedRegion (walkP d hclosed hsimple) := ⟨C, hCfin⟩
    letI : Unique (jcb_BoundedRegion (walkP d hclosed hsimple)) :=
      jcb_uniqueBoundedRegion_of_nullity_one (walkP d hclosed hsimple)
        (walkSubgraph_nullity_one d hclosed hsimple)
    have hEq : current = inner := Subsingleton.elim _ _
    rw [mem_interiorCells]
    apply (innerComponent d hclosed hsimple hreflexfree).mem_supp_iff (cellFace p) |>.mpr
    change C = innerComponent d hclosed hsimple hreflexfree
    exact congrArg Subtype.val hEq

end Walk

end StatMech.Onsager.WalkCellRegion
