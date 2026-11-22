/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.PolygonalWorkspace
public meta import CSLibExt.Planning.MotionPlanning.PolygonalWorkspace
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Polygonal workspace tests

Concrete fixtures (unit square, slanted quadrilateral, slanted triangle),
simplicity regression checks, and axiom probes for
`CSLibExt.Planning.MotionPlanning.PolygonalWorkspace`.
-/

namespace Cslib.Planning.MotionPlanning.PolygonalWorkspace

open Set

/-- Unit-square corners (counterclockwise from the origin). -/
def sqA : plane := !₂[0, 0]
def sqB : plane := !₂[1, 0]
def sqC : plane := !₂[1, 1]
def sqD : plane := !₂[0, 1]
/-- The unit-square vertex list. -/
def squareVerts : List plane := [sqA, sqB, sqC, sqD]
/-- A slanted quadrilateral with x-coordinates 0, 3, 4, 1. -/
def slA : plane := !₂[0, 0]
def slB : plane := !₂[3, 1]
def slC : plane := !₂[4, 3]
def slD : plane := !₂[1, 2]
/-- The slanted-quadrilateral vertex list. -/
def slantedVerts : List plane := [slA, slB, slC, slD]
/-- A triangle with vertices (0, 0), (2, 0), (0, 1). -/
def triA : plane := !₂[0, 0]
def triB : plane := !₂[2, 0]
def triC : plane := !₂[0, 1]
/-- The triangle vertex list. -/
def triangleVerts : List plane := [triA, triB, triC]
/-- DEFINITIONAL computations: x-coordinates of the example points. -/
theorem sqA_x : sqA 0 = 0 := by simp [sqA]
theorem sqB_x : sqB 0 = 1 := by simp [sqB]
theorem sqC_x : sqC 0 = 1 := by simp [sqC]
theorem sqD_x : sqD 0 = 0 := by simp [sqD]
theorem slA_x : slA 0 = 0 := by simp [slA]
theorem slB_x : slB 0 = 3 := by simp [slB]
theorem slC_x : slC 0 = 4 := by simp [slC]
theorem slD_x : slD 0 = 1 := by simp [slD]
/-- DEFINITIONAL computations: y-coordinates of the slanted points. -/
theorem slA_y : slA 1 = 0 := by simp [slA]
theorem slB_y : slB 1 = 1 := by simp [slB]
theorem slC_y : slC 1 = 3 := by simp [slC]
theorem slD_y : slD 1 = 2 := by simp [slD]
/-- The unit square has x-coordinates `[0, 1, 1, 0]`. -/
theorem xCoordsOf_squareVerts : xCoordsOf squareVerts = [0, 1, 1, 0] := by
  simp [xCoordsOf, squareVerts, sqA_x, sqB_x, sqC_x, sqD_x]
/-- The slanted quadrilateral has x-coordinates `[0, 3, 4, 1]`. -/
theorem xCoordsOf_slantedVerts : xCoordsOf slantedVerts = [0, 3, 4, 1] := by
  simp [xCoordsOf, slantedVerts, slA_x, slB_x, slC_x, slD_x]
/-- The unit square with no holes has vertex count 4. -/
theorem vertexCountOf_squareVerts : vertexCountOf squareVerts [] = 4 := rfl
/-- The axis-aligned unit square is NOT in general position: two pairs of
vertices share an x-coordinate. -/
theorem not_generalPositionOf_squareVerts : ¬ generalPositionOf squareVerts := by
  unfold generalPositionOf
  rw [xCoordsOf_squareVerts]
  intro h
  obtain ⟨hhead, _⟩ := List.pairwise_cons.mp h
  exact hhead 0 (by simp) rfl
/-- The slanted quadrilateral IS in general position. -/
theorem generalPositionOf_slantedVerts : generalPositionOf slantedVerts := by
  unfold generalPositionOf
  rw [xCoordsOf_slantedVerts]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ List.Pairwise.nil)))
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> norm_num
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> norm_num
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    norm_num
  · intro b hb
    simp at hb
/-- The slanted vertices are pairwise distinct (x-coordinates differ). -/
theorem slA_ne_slB : slA ≠ slB := by
  intro h
  have hx := congrArg (fun q : plane => q 0) h
  rw [slA_x, slB_x] at hx
  norm_num at hx
/-- The slanted vertices are pairwise distinct (x-coordinates differ). -/
theorem slA_ne_slC : slA ≠ slC := by
  intro h
  have hx := congrArg (fun q : plane => q 0) h
  rw [slA_x, slC_x] at hx
  norm_num at hx
/-- The slanted vertices are pairwise distinct (x-coordinates differ). -/
theorem slA_ne_slD : slA ≠ slD := by
  intro h
  have hx := congrArg (fun q : plane => q 0) h
  rw [slA_x, slD_x] at hx
  norm_num at hx
/-- The slanted vertices are pairwise distinct (x-coordinates differ). -/
theorem slB_ne_slC : slB ≠ slC := by
  intro h
  have hx := congrArg (fun q : plane => q 0) h
  rw [slB_x, slC_x] at hx
  norm_num at hx
/-- The slanted vertices are pairwise distinct (x-coordinates differ). -/
theorem slB_ne_slD : slB ≠ slD := by
  intro h
  have hx := congrArg (fun q : plane => q 0) h
  rw [slB_x, slD_x] at hx
  norm_num at hx
/-- The slanted vertices are pairwise distinct (x-coordinates differ). -/
theorem slC_ne_slD : slC ≠ slD := by
  intro h
  have hx := congrArg (fun q : plane => q 0) h
  rw [slC_x, slD_x] at hx
  norm_num at hx
/-- Non-adjacent slanted edge occurrences 0 and 2 are disjoint. -/
theorem seg_AB_CD_disjoint : Disjoint (segment ℝ slA slB) (segment ℝ slC slD) := by
  rw [Set.disjoint_left]
  rintro p hAB hCD
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hAB
  obtain ⟨c, d, hc, hd, hcd, heq⟩ := hCD
  have e0 : c * 4 + d * 1 = a * 0 + b * 3 := congrArg (fun q : plane => q 0) heq
  have e1 : c * 3 + d * 2 = a * 0 + b * 1 := congrArg (fun q : plane => q 1) heq
  linarith
/-- Non-adjacent slanted edge occurrences 1 and 3 are disjoint. -/
theorem seg_BC_DA_disjoint : Disjoint (segment ℝ slB slC) (segment ℝ slD slA) := by
  rw [Set.disjoint_left]
  rintro p hBC hDA
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hBC
  obtain ⟨c, d, hc, hd, hcd, heq⟩ := hDA
  have e0 : c * 1 + d * 0 = a * 3 + b * 4 := congrArg (fun q : plane => q 0) heq
  have e1 : c * 2 + d * 0 = a * 1 + b * 3 := congrArg (fun q : plane => q 1) heq
  linarith
/-- Adjacent slanted edge occurrences 0 and 1 meet exactly in `slB`. -/
theorem seg_AB_BC_inter :
    (segment ℝ slA slB ∩ segment ℝ slB slC : Set plane) = {slB} := by
  ext p
  constructor
  · rintro ⟨hAB, hBC⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hAB
    obtain ⟨c, d, hc, hd, hcd, heq⟩ := hBC
    have e0 : c * 3 + d * 4 = a * 0 + b * 3 := congrArg (fun q : plane => q 0) heq
    have e1 : c * 1 + d * 3 = a * 0 + b * 1 := congrArg (fun q : plane => q 1) heq
    have hd0 : d = 0 := by linarith
    have hc1 : c = 1 := by linarith
    have hb1 : b = 1 := by linarith
    have ha0 : a = 0 := by linarith
    simp only [Set.mem_singleton_iff]
    rw [ha0, hb1]
    simp
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨right_mem_segment ℝ slA slB, left_mem_segment ℝ slB slC⟩
/-- Adjacent slanted edge occurrences 1 and 2 meet exactly in `slC`. -/
theorem seg_BC_CD_inter :
    (segment ℝ slB slC ∩ segment ℝ slC slD : Set plane) = {slC} := by
  ext p
  constructor
  · rintro ⟨hBC, hCD⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hBC
    obtain ⟨c, d, hc, hd, hcd, heq⟩ := hCD
    have e0 : c * 4 + d * 1 = a * 3 + b * 4 := congrArg (fun q : plane => q 0) heq
    have e1 : c * 3 + d * 2 = a * 1 + b * 3 := congrArg (fun q : plane => q 1) heq
    have hc1 : c = 1 := by linarith
    have hd0 : d = 0 := by linarith
    have hb1 : b = 1 := by linarith
    have ha0 : a = 0 := by linarith
    simp only [Set.mem_singleton_iff]
    rw [ha0, hb1]
    simp
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨right_mem_segment ℝ slB slC, left_mem_segment ℝ slC slD⟩
/-- Adjacent slanted edge occurrences 2 and 3 meet exactly in `slD`. -/
theorem seg_CD_DA_inter :
    (segment ℝ slC slD ∩ segment ℝ slD slA : Set plane) = {slD} := by
  ext p
  constructor
  · rintro ⟨hCD, hDA⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hCD
    obtain ⟨c, d, hc, hd, hcd, heq⟩ := hDA
    have e0 : c * 1 + d * 0 = a * 4 + b * 1 := congrArg (fun q : plane => q 0) heq
    have e1 : c * 2 + d * 0 = a * 3 + b * 2 := congrArg (fun q : plane => q 1) heq
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    have hc1 : c = 1 := by linarith
    have hd0 : d = 0 := by linarith
    simp only [Set.mem_singleton_iff]
    rw [ha0, hb1]
    simp
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨right_mem_segment ℝ slC slD, left_mem_segment ℝ slD slA⟩
/-- Adjacent slanted edge occurrences 3 and 0 meet exactly in `slA`. -/
theorem seg_DA_AB_inter :
    (segment ℝ slD slA ∩ segment ℝ slA slB : Set plane) = {slA} := by
  ext p
  constructor
  · rintro ⟨hDA, hAB⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hDA
    obtain ⟨c, d, hc, hd, hcd, heq⟩ := hAB
    have e0 : c * 0 + d * 3 = a * 1 + b * 0 := congrArg (fun q : plane => q 0) heq
    have e1 : c * 0 + d * 1 = a * 2 + b * 0 := congrArg (fun q : plane => q 1) heq
    have ha0 : a = 0 := by linarith
    have hd0 : d = 0 := by linarith
    have hb1 : b = 1 := by linarith
    have hc1 : c = 1 := by linarith
    simp only [Set.mem_singleton_iff]
    rw [ha0, hb1]
    simp
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨right_mem_segment ℝ slD slA, left_mem_segment ℝ slA slB⟩
/-- Adjacent slanted-triangle edge occurrences 1 and 2 meet exactly in `slC`. -/
theorem seg_BC_CA_inter :
    (segment ℝ slB slC ∩ segment ℝ slC slA : Set plane) = {slC} := by
  ext p
  constructor
  · rintro ⟨hBC, hCA⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hBC
    obtain ⟨c, d, hc, hd, hcd, heq⟩ := hCA
    have e0 : c * 4 + d * 0 = a * 3 + b * 4 := congrArg (fun q : plane => q 0) heq
    have e1 : c * 3 + d * 0 = a * 1 + b * 3 := congrArg (fun q : plane => q 1) heq
    have hc1 : c = 1 := by linarith
    have hd0 : d = 0 := by linarith
    have hb1 : b = 1 := by linarith
    have ha0 : a = 0 := by linarith
    simp only [Set.mem_singleton_iff]
    rw [ha0, hb1]
    simp
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨right_mem_segment ℝ slB slC, left_mem_segment ℝ slC slA⟩
/-- Adjacent slanted-triangle edge occurrences 2 and 0 meet exactly in `slA`. -/
theorem seg_CA_AB_inter :
    (segment ℝ slC slA ∩ segment ℝ slA slB : Set plane) = {slA} := by
  ext p
  constructor
  · rintro ⟨hCA, hAB⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hCA
    obtain ⟨c, d, hc, hd, hcd, heq⟩ := hAB
    have e0 : c * 0 + d * 3 = a * 4 + b * 0 := congrArg (fun q : plane => q 0) heq
    have e1 : c * 0 + d * 1 = a * 3 + b * 0 := congrArg (fun q : plane => q 1) heq
    have ha0 : a = 0 := by linarith
    have hd0 : d = 0 := by linarith
    have hb1 : b = 1 := by linarith
    have hc1 : c = 1 := by linarith
    simp only [Set.mem_singleton_iff]
    rw [ha0, hb1]
    simp
  · intro hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨right_mem_segment ℝ slC slA, left_mem_segment ℝ slA slB⟩
/-- The slanted vertices have no duplicates. -/
theorem nodup_slantedVerts : List.Nodup slantedVerts := by
  have hvs : slantedVerts = [slA, slB, slC, slD] := rfl
  rw [hvs]
  simp only [List.nodup_cons]
  refine ⟨?_, ?_, ?_, ?_, List.nodup_nil⟩
  · simp [slA_ne_slB, slA_ne_slC, slA_ne_slD]
  · simp [slB_ne_slC, slB_ne_slD]
  · simp [slC_ne_slD]
  · simp
/-- No slanted edge occurrence is degenerate. -/
theorem noZero_slantedVerts : ∀ e ∈ cyclicEdges slantedVerts, e.1 ≠ e.2 := by
  have heq : cyclicEdges slantedVerts =
      [(slA, slB), (slB, slC), (slC, slD), (slD, slA)] := rfl
  intro e he
  rw [heq] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact slA_ne_slB
  · exact slB_ne_slC
  · exact slC_ne_slD
  · exact slA_ne_slD.symm
/-- The slanted quadrilateral satisfies occurrence-based simplicity. -/
theorem simple_slantedVerts : PolySimple slantedVerts := by
  refine ⟨by decide, nodup_slantedVerts, noZero_slantedVerts, ?_⟩
  intro i j hi hj hne
  have hi4 : i < 4 := hi
  have hj4 : j < 4 := hj
  interval_cases i <;> interval_cases j
  · exact absurd rfl hne
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slA, slB} : Set plane) ∩ ({slB, slC} : Set plane)),
        (segment ℝ slA slB ∩ segment ℝ slB slC : Set plane) = {p}
      exact ⟨slB, by simp, seg_AB_BC_inter⟩
    · show edgeAdjacent 0 1 4
      unfold edgeAdjacent
      decide
  · refine ⟨fun h => absurd h ?_, fun _ => ?_⟩
    · show ¬ edgeAdjacent 0 2 4
      unfold edgeAdjacent
      decide
    · show Disjoint (segment ℝ slA slB) (segment ℝ slC slD)
      exact seg_AB_CD_disjoint
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slA, slB} : Set plane) ∩ ({slD, slA} : Set plane)),
        (segment ℝ slA slB ∩ segment ℝ slD slA : Set plane) = {p}
      refine ⟨slA, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_DA_AB_inter
    · show edgeAdjacent 0 3 4
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slB, slC} : Set plane) ∩ ({slA, slB} : Set plane)),
        (segment ℝ slB slC ∩ segment ℝ slA slB : Set plane) = {p}
      refine ⟨slB, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_AB_BC_inter
    · show edgeAdjacent 1 0 4
      unfold edgeAdjacent
      decide
  · exact absurd rfl hne
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slB, slC} : Set plane) ∩ ({slC, slD} : Set plane)),
        (segment ℝ slB slC ∩ segment ℝ slC slD : Set plane) = {p}
      exact ⟨slC, by simp, seg_BC_CD_inter⟩
    · show edgeAdjacent 1 2 4
      unfold edgeAdjacent
      decide
  · refine ⟨fun h => absurd h ?_, fun _ => ?_⟩
    · show ¬ edgeAdjacent 1 3 4
      unfold edgeAdjacent
      decide
    · show Disjoint (segment ℝ slB slC) (segment ℝ slD slA)
      exact seg_BC_DA_disjoint
  · refine ⟨fun h => absurd h ?_, fun _ => ?_⟩
    · show ¬ edgeAdjacent 2 0 4
      unfold edgeAdjacent
      decide
    · show Disjoint (segment ℝ slC slD) (segment ℝ slA slB)
      exact seg_AB_CD_disjoint.symm
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slC, slD} : Set plane) ∩ ({slB, slC} : Set plane)),
        (segment ℝ slC slD ∩ segment ℝ slB slC : Set plane) = {p}
      refine ⟨slC, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_BC_CD_inter
    · show edgeAdjacent 2 1 4
      unfold edgeAdjacent
      decide
  · exact absurd rfl hne
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slC, slD} : Set plane) ∩ ({slD, slA} : Set plane)),
        (segment ℝ slC slD ∩ segment ℝ slD slA : Set plane) = {p}
      exact ⟨slD, by simp, seg_CD_DA_inter⟩
    · show edgeAdjacent 2 3 4
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slD, slA} : Set plane) ∩ ({slA, slB} : Set plane)),
        (segment ℝ slD slA ∩ segment ℝ slA slB : Set plane) = {p}
      exact ⟨slA, by simp, seg_DA_AB_inter⟩
    · show edgeAdjacent 3 0 4
      unfold edgeAdjacent
      decide
  · refine ⟨fun h => absurd h ?_, fun _ => ?_⟩
    · show ¬ edgeAdjacent 3 1 4
      unfold edgeAdjacent
      decide
    · show Disjoint (segment ℝ slD slA) (segment ℝ slB slC)
      exact seg_BC_DA_disjoint.symm
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slD, slA} : Set plane) ∩ ({slC, slD} : Set plane)),
        (segment ℝ slD slA ∩ segment ℝ slC slD : Set plane) = {p}
      refine ⟨slD, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_CD_DA_inter
    · show edgeAdjacent 3 2 4
      unfold edgeAdjacent
      decide
  · exact absurd rfl hne
theorem Workspace.not_GeneralPosition_square (W : Workspace)
    (hv : W.outer.vertices = squareVerts) (h : W.holes = []) :
    ¬ W.GeneralPosition := by
  unfold Workspace.GeneralPosition
  rw [W.allVertices_of_holes_nil h, hv]
  exact not_generalPositionOf_squareVerts
/-- Any hole-free workspace on the slanted quadrilateral is in general
position. -/
theorem Workspace.generalPosition_slanted (W : Workspace)
    (hv : W.outer.vertices = slantedVerts) (h : W.holes = []) :
    W.GeneralPosition := by
  unfold Workspace.GeneralPosition
  rw [W.allVertices_of_holes_nil h, hv]
  exact generalPositionOf_slantedVerts
/-- DEFINITIONAL computation: the triangle edge list. -/
theorem cyclicEdges_triangle :
    cyclicEdges triangleVerts = [(triA, triB), (triB, triC), (triC, triA)] := rfl
/-- The triangle boundary chain is the union of its three closed segments. -/
theorem boundarySet_triangle :
    boundarySet triangleVerts =
      segment ℝ triA triB ∪ segment ℝ triB triC ∪ segment ℝ triC triA := by
  ext p
  rw [mem_boundarySet_iff, cyclicEdges_triangle]
  simp only [Set.mem_union]
  constructor
  · rintro ⟨e, he, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact Or.inl (Or.inl hmem)
    · exact Or.inl (Or.inr hmem)
    · exact Or.inr hmem
  · rintro ((h | h) | h)
    · exact ⟨(triA, triB), by simp, h⟩
    · exact ⟨(triB, triC), by simp, h⟩
    · exact ⟨(triC, triA), by simp, h⟩
/-- Pinched two-triangle vertex points (the first point repeats). -/
def pinA : plane := !₂[2, 0]
def pinB : plane := !₂[0, 1]
def pinC : plane := !₂[0, 0]
def pinD : plane := !₂[4, 0]
def pinE : plane := !₂[2, 1]
/-- The pinched vertex list `[(2,0),(0,1),(0,0),(2,0),(4,0),(2,1)]`: two
triangles pinched at the repeated vertex `(2,0)`. -/
def pinchedVerts : List plane := [pinA, pinB, pinC, pinA, pinD, pinE]
/-- The pinched vertex list has a duplicate, so it is not nodup. -/
theorem not_nodup_pinchedVerts : ¬ List.Nodup pinchedVerts := by
  have hvs : pinchedVerts = [pinA, pinB, pinC, pinA, pinD, pinE] := rfl
  rw [hvs, List.nodup_cons]
  rintro ⟨hmem, -⟩
  exact hmem (by simp)
/-- The pinched vertex list fails occurrence-based simplicity. -/
theorem not_simple_pinchedVerts : ¬ PolySimple pinchedVerts := by
  rintro ⟨-, hnodup, -, -⟩
  exact not_nodup_pinchedVerts hnodup
/-- A duplicated-vertex list `[A,B,C,A,B,C]`. -/
def dupVerts : List plane := [triA, triB, triC, triA, triB, triC]
/-- The duplicated-vertex list is not nodup. -/
theorem not_nodup_dupVerts : ¬ List.Nodup dupVerts := by
  have hvs : dupVerts = [triA, triB, triC, triA, triB, triC] := rfl
  rw [hvs, List.nodup_cons]
  rintro ⟨hmem, -⟩
  exact hmem (by simp)
/-- A slanted triangle reusing the first three slanted vertices. -/
def slantTriVerts : List plane := [slA, slB, slC]
/-- DEFINITIONAL: the closed slanted triangle as an explicit intersection of
three closed half-planes. -/
def slantTriRegion : Set plane :=
  {p | p 0 - 3 * p 1 ≤ 0 ∧ 2 * p 0 - p 1 ≤ 5 ∧ 0 ≤ 3 * p 0 - 4 * p 1}
/-- DEFINITIONAL: the open slanted triangle via strict inequalities. -/
def slantTriInterior : Set plane :=
  {p | p 0 - 3 * p 1 < 0 ∧ 2 * p 0 - p 1 < 5 ∧ 0 < 3 * p 0 - 4 * p 1}
/-- The slanted triangle has three vertices. -/
theorem len_ge_slantTriVerts : 3 ≤ slantTriVerts.length := by decide
/-- The explicit slanted-triangle region is closed. -/
theorem isClosed_slantTriRegion : IsClosed slantTriRegion := by
  have cf1 : Continuous fun p : plane => p 0 - 3 * p 1 := by fun_prop
  have cg1 : Continuous fun _ : plane => (0 : ℝ) := continuous_const
  have h1 : IsClosed {p : plane | p 0 - 3 * p 1 ≤ 0} := isClosed_le cf1 cg1
  have cf2 : Continuous fun p : plane => 2 * p 0 - p 1 := by fun_prop
  have cg2 : Continuous fun _ : plane => (5 : ℝ) := continuous_const
  have h2 : IsClosed {p : plane | 2 * p 0 - p 1 ≤ 5} := isClosed_le cf2 cg2
  have cf3 : Continuous fun p : plane => 3 * p 0 - 4 * p 1 := by fun_prop
  have cg3 : Continuous fun _ : plane => (0 : ℝ) := continuous_const
  have h3 : IsClosed {p : plane | 0 ≤ 3 * p 0 - 4 * p 1} := isClosed_le cg3 cf3
  have hsub : slantTriRegion =
      {p : plane | p 0 - 3 * p 1 ≤ 0} ∩
        ({p : plane | 2 * p 0 - p 1 ≤ 5} ∩ {p : plane | 0 ≤ 3 * p 0 - 4 * p 1}) :=
    rfl
  rw [hsub]
  exact IsClosed.inter h1 (IsClosed.inter h2 h3)
/-- The explicit slanted-triangle region is bounded. -/
theorem isBounded_slantTriRegion : Bornology.IsBounded slantTriRegion := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨7, fun p hp => ?_⟩
  obtain ⟨hc1, hc2, hc3⟩ := hp
  have h0lo : 0 ≤ p 0 := by linarith
  have h0hi : p 0 ≤ 4 := by linarith
  have h1lo : 0 ≤ p 1 := by linarith
  have h1hi : p 1 ≤ 3 := by linarith
  have g0 : p.ofLp 0 = p 0 := rfl
  have g1 : p.ofLp 1 = p 1 := rfl
  have hsq : ‖p‖ ^ 2 ≤ 49 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, g0, g1]
    have hnn : (0 : ℝ) ≤ ‖p 0‖ ^ 2 + ‖p 1‖ ^ 2 := by positivity
    rw [Real.sq_sqrt hnn]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [mul_nonneg (sub_nonneg.mpr h0hi) (show (0 : ℝ) ≤ 4 + p 0 by linarith),
      mul_nonneg (sub_nonneg.mpr h1hi) (show (0 : ℝ) ≤ 3 + p 1 by linarith)]
  nlinarith [hsq, norm_nonneg p, show (0 : ℝ) ≤ ‖p‖ + 7 by positivity]
/-- The open slanted triangle is open. -/
theorem isOpen_slantTriInterior : IsOpen slantTriInterior := by
  have cf1 : Continuous fun p : plane => p 0 - 3 * p 1 := by fun_prop
  have cg1 : Continuous fun _ : plane => (0 : ℝ) := continuous_const
  have h1 : IsOpen {p : plane | p 0 - 3 * p 1 < 0} := isOpen_lt cf1 cg1
  have cf2 : Continuous fun p : plane => 2 * p 0 - p 1 := by fun_prop
  have cg2 : Continuous fun _ : plane => (5 : ℝ) := continuous_const
  have h2 : IsOpen {p : plane | 2 * p 0 - p 1 < 5} := isOpen_lt cf2 cg2
  have cf3 : Continuous fun p : plane => 3 * p 0 - 4 * p 1 := by fun_prop
  have cg3 : Continuous fun _ : plane => (0 : ℝ) := continuous_const
  have h3 : IsOpen {p : plane | 0 < 3 * p 0 - 4 * p 1} := isOpen_lt cg3 cf3
  have hsub : slantTriInterior =
      {p : plane | p 0 - 3 * p 1 < 0} ∩
        ({p : plane | 2 * p 0 - p 1 < 5} ∩ {p : plane | 0 < 3 * p 0 - 4 * p 1}) :=
    rfl
  rw [hsub]
  exact IsOpen.inter h1 (IsOpen.inter h2 h3)
/-- The open slanted triangle lies inside the closed region. -/
theorem slantTriInterior_subset_region : slantTriInterior ⊆ slantTriRegion := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3⟩
/-- An interior point of the slanted triangle. -/
def triInteriorPoint : plane := !₂[2, 1]
/-- The interior point lies strictly inside. -/
theorem interiorPoint_mem_slantTriInterior : triInteriorPoint ∈ slantTriInterior := by
  have c0 : triInteriorPoint 0 = 2 := by simp [triInteriorPoint]
  have c1 : triInteriorPoint 1 = 1 := by simp [triInteriorPoint]
  show triInteriorPoint 0 - 3 * triInteriorPoint 1 < 0 ∧
    2 * triInteriorPoint 0 - triInteriorPoint 1 < 5 ∧
    0 < 3 * triInteriorPoint 0 - 4 * triInteriorPoint 1
  rw [c0, c1]
  norm_num
/-- The explicit slanted-triangle region has nonempty interior. -/
theorem interiorNonempty_slantTriRegion : (interior slantTriRegion).Nonempty := by
  refine ⟨triInteriorPoint, ?_⟩
  exact interior_maximal slantTriInterior_subset_region isOpen_slantTriInterior
    interiorPoint_mem_slantTriInterior
/-- The slanted-triangle vertices have no duplicates. -/
theorem nodup_slantTriVerts : List.Nodup slantTriVerts := by
  have hvs : slantTriVerts = [slA, slB, slC] := rfl
  rw [hvs]
  simp only [List.nodup_cons]
  refine ⟨?_, ?_, ?_, List.nodup_nil⟩
  · simp [slA_ne_slB, slA_ne_slC]
  · simp [slB_ne_slC]
  · simp
/-- No slanted-triangle edge occurrence is degenerate. -/
theorem noZero_slantTriVerts : ∀ e ∈ cyclicEdges slantTriVerts, e.1 ≠ e.2 := by
  have heq : cyclicEdges slantTriVerts = [(slA, slB), (slB, slC), (slC, slA)] := rfl
  intro e he
  rw [heq] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact slA_ne_slB
  · exact slB_ne_slC
  · exact slA_ne_slC.symm
/-- The slanted triangle satisfies occurrence-based simplicity. -/
theorem simple_slantTriVerts : PolySimple slantTriVerts := by
  refine ⟨by decide, nodup_slantTriVerts, noZero_slantTriVerts, ?_⟩
  intro i j hi hj hne
  have hi3 : i < 3 := hi
  have hj3 : j < 3 := hj
  interval_cases i <;> interval_cases j
  · exact absurd rfl hne
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slA, slB} : Set plane) ∩ ({slB, slC} : Set plane)),
        (segment ℝ slA slB ∩ segment ℝ slB slC : Set plane) = {p}
      exact ⟨slB, by simp, seg_AB_BC_inter⟩
    · show edgeAdjacent 0 1 3
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slA, slB} : Set plane) ∩ ({slC, slA} : Set plane)),
        (segment ℝ slA slB ∩ segment ℝ slC slA : Set plane) = {p}
      refine ⟨slA, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_CA_AB_inter
    · show edgeAdjacent 0 2 3
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slB, slC} : Set plane) ∩ ({slA, slB} : Set plane)),
        (segment ℝ slB slC ∩ segment ℝ slA slB : Set plane) = {p}
      refine ⟨slB, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_AB_BC_inter
    · show edgeAdjacent 1 0 3
      unfold edgeAdjacent
      decide
  · exact absurd rfl hne
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slB, slC} : Set plane) ∩ ({slC, slA} : Set plane)),
        (segment ℝ slB slC ∩ segment ℝ slC slA : Set plane) = {p}
      exact ⟨slC, by simp, seg_BC_CA_inter⟩
    · show edgeAdjacent 1 2 3
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slC, slA} : Set plane) ∩ ({slA, slB} : Set plane)),
        (segment ℝ slC slA ∩ segment ℝ slA slB : Set plane) = {p}
      exact ⟨slA, by simp, seg_CA_AB_inter⟩
    · show edgeAdjacent 2 0 3
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({slC, slA} : Set plane) ∩ ({slB, slC} : Set plane)),
        (segment ℝ slC slA ∩ segment ℝ slB slC : Set plane) = {p}
      refine ⟨slC, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_BC_CA_inter
    · show edgeAdjacent 2 1 3
      unfold edgeAdjacent
      decide
  · exact absurd rfl hne
theorem xCoordsOf_slantTriVerts : xCoordsOf slantTriVerts = [0, 3, 4] := by
  simp [xCoordsOf, slantTriVerts, slA_x, slB_x, slC_x]
/-- The slanted triangle with no holes has vertex count 3. -/
theorem vertexCountOf_slantTriVerts : vertexCountOf slantTriVerts [] = 3 := rfl
/-- The slanted triangle IS in general position. -/
theorem generalPositionOf_slantTriVerts : generalPositionOf slantTriVerts := by
  unfold generalPositionOf
  rw [xCoordsOf_slantTriVerts]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    List.Pairwise.nil))
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> norm_num
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl
    norm_num
  · intro b hb
    simp at hb

/- Former stage-2 need, now discharged below by `frontier_slantTriRegion`:
the `boundary_eq` coupling for the explicit slanted triangle,
`frontier slantTriRegion = boundarySet slantTriVerts`.
Both inclusions used explicit witnesses: every boundary-chain point lies in
`slantTriRegion` but outside its interior (outward normal witnesses per edge),
and every region point outside the interior lies on an edge segment (via
`slantTriInterior_subset_region`). With it, `slantTriVerts` with
`slantTriRegion` assembled into `slantTriPoly` (via `len_ge_slantTriVerts`,
`isClosed_slantTriRegion`, `isBounded_slantTriRegion`), and then into
`slantTriWorkspace`. -/
/-- Inline example checks (acceptance tests). -/
example : vertexCountOf squareVerts [] = 4 := vertexCountOf_squareVerts
example : ¬ generalPositionOf squareVerts := not_generalPositionOf_squareVerts
example : generalPositionOf slantedVerts := generalPositionOf_slantedVerts
example : boundarySet triangleVerts =
    segment ℝ triA triB ∪ segment ℝ triB triC ∪ segment ℝ triC triA :=
  boundarySet_triangle
example (W : Workspace) : IsOpen W.freeSpace := W.isOpen_freeSpace
example (W : Workspace) (hlen : W.outer.vertices.length = 4)
    (h : W.holes = []) : W.vertexCount = 4 := W.vertexCount_square hlen h
example : PolySimple slantedVerts := simple_slantedVerts
example : PolySimple slantTriVerts := simple_slantTriVerts
example : ¬ PolySimple pinchedVerts := not_simple_pinchedVerts
example : ¬ List.Nodup dupVerts := not_nodup_dupVerts
example : vertexCountOf slantTriVerts [] = 3 := vertexCountOf_slantTriVerts
example : generalPositionOf slantTriVerts := generalPositionOf_slantTriVerts
#print axioms Workspace.isOpen_freeSpace
#print axioms isClosed_holeUnion
#print axioms vertexCountOf_squareVerts
#print axioms not_generalPositionOf_squareVerts
#print axioms generalPositionOf_slantedVerts
#print axioms boundarySet_triangle
#print axioms Workspace.vertexCount_square
#print axioms Workspace.not_GeneralPosition_square
#print axioms Workspace.generalPosition_slanted
#print axioms simple_slantedVerts
#print axioms simple_slantTriVerts
#print axioms not_simple_pinchedVerts
#print axioms not_nodup_dupVerts
#print axioms not_nodup_pinchedVerts
#print axioms isClosed_slantTriRegion
#print axioms isBounded_slantTriRegion
#print axioms interiorNonempty_slantTriRegion
#print axioms vertexCountOf_slantTriVerts
#print axioms generalPositionOf_slantTriVerts

/- Frontier of the explicit slanted-triangle region (construction stage 2a).

The closed slanted triangle is an intersection of three closed half-planes;
its frontier is the boundary chain of its three sides. This is the polygonal
boundary representation in LaValle, Planning Algorithms, Section 6.2.1. -/

/-- Witness direction: unit x-step for outward normals of the first two edges. -/
def frontier_e0 : plane := !₂[1, 0]

/-- Witness direction: unit y-step for the outward normal of the third edge. -/
def frontier_e1 : plane := !₂[0, 1]

theorem frontier_e0_norm : ‖frontier_e0‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [frontier_e0]

theorem frontier_e1_norm : ‖frontier_e1‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [frontier_e1]

theorem frontier_dist_e0 (p : plane) (t : ℝ) :
    dist (p + t • frontier_e0) p = |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, frontier_e0_norm, mul_one,
    Real.norm_eq_abs]

theorem frontier_dist_e1 (p : plane) (t : ℝ) :
    dist (p + t • frontier_e1) p = |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, frontier_e1_norm, mul_one,
    Real.norm_eq_abs]

theorem frontier_add_e0_c0 (p : plane) (t : ℝ) : (p + t • frontier_e0) 0 = p 0 + t := by
  simp [frontier_e0]

theorem frontier_add_e0_c1 (p : plane) (t : ℝ) : (p + t • frontier_e0) 1 = p 1 := by
  simp [frontier_e0]

theorem frontier_add_e1_c0 (p : plane) (t : ℝ) : (p + t • frontier_e1) 0 = p 0 := by
  simp [frontier_e1]

theorem frontier_add_e1_c1 (p : plane) (t : ℝ) : (p + t • frontier_e1) 1 = p 1 + t := by
  simp [frontier_e1]

theorem frontier_cont_f1 : Continuous (fun p : plane => p 0 - 3 * p 1) :=
  (PiLp.continuous_apply 2 (fun _ => ℝ) 0).sub
    (continuous_const.mul (PiLp.continuous_apply 2 (fun _ => ℝ) 1))

theorem frontier_cont_f2 : Continuous (fun p : plane => 2 * p 0 - p 1) :=
  ((continuous_const : Continuous fun _ : plane => (2:ℝ)).mul
    (PiLp.continuous_apply 2 (fun _ => ℝ) 0)).sub
    (PiLp.continuous_apply 2 (fun _ => ℝ) 1)

theorem frontier_cont_f3 : Continuous (fun p : plane => 3 * p 0 - 4 * p 1) :=
  (((continuous_const : Continuous fun _ : plane => (3:ℝ)).mul
    (PiLp.continuous_apply 2 (fun _ => ℝ) 0)).sub
    ((continuous_const : Continuous fun _ : plane => (4:ℝ)).mul
      (PiLp.continuous_apply 2 (fun _ => ℝ) 1)))

theorem frontier_closed_region : IsClosed slantTriRegion := by
  have h1 : IsClosed {p : plane | p 0 - 3 * p 1 ≤ 0} :=
    isClosed_le frontier_cont_f1 (continuous_const : Continuous fun _ : plane => (0:ℝ))
  have h2 : IsClosed {p : plane | 2 * p 0 - p 1 ≤ 5} :=
    isClosed_le frontier_cont_f2 (continuous_const : Continuous fun _ : plane => (5:ℝ))
  have h3 : IsClosed {p : plane | (0:ℝ) ≤ 3 * p 0 - 4 * p 1} :=
    isClosed_le (continuous_const : Continuous fun _ : plane => (0:ℝ)) frontier_cont_f3
  have heq : slantTriRegion =
      {p : plane | p 0 - 3 * p 1 ≤ 0} ∩
      ({p : plane | 2 * p 0 - p 1 ≤ 5} ∩
        {p : plane | (0:ℝ) ≤ 3 * p 0 - 4 * p 1}) := rfl
  rw [heq]
  exact h1.inter (h2.inter h3)

theorem frontier_open_interiorSet : IsOpen slantTriInterior := by
  have h1 : IsOpen {p : plane | p 0 - 3 * p 1 < 0} :=
    isOpen_lt frontier_cont_f1 (continuous_const : Continuous fun _ : plane => (0:ℝ))
  have h2 : IsOpen {p : plane | 2 * p 0 - p 1 < 5} :=
    isOpen_lt frontier_cont_f2 (continuous_const : Continuous fun _ : plane => (5:ℝ))
  have h3 : IsOpen {p : plane | (0:ℝ) < 3 * p 0 - 4 * p 1} :=
    isOpen_lt (continuous_const : Continuous fun _ : plane => (0:ℝ)) frontier_cont_f3
  have heq : slantTriInterior =
      {p : plane | p 0 - 3 * p 1 < 0} ∩
      ({p : plane | 2 * p 0 - p 1 < 5} ∩
        {p : plane | (0:ℝ) < 3 * p 0 - 4 * p 1}) := rfl
  rw [heq]
  exact h1.inter (h2.inter h3)

theorem frontier_subset_interior : slantTriInterior ⊆ slantTriRegion := by
  intro p hp
  simp only [slantTriInterior, slantTriRegion, mem_ofPred_eq] at hp ⊢
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3⟩

/-- Points on the first edge line are outside the interior. -/
theorem frontier_not_mem_of_f1 (p : plane) (h : p 0 - 3 * p 1 = 0) :
    p ∉ interior slantTriRegion := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hεpos, hεsub⟩ := hmem
  set q := p + (ε / 2) • frontier_e0 with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, frontier_dist_e0, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  have hqmem := hεsub hqball
  simp only [slantTriRegion, mem_ofPred_eq] at hqmem
  obtain ⟨h1, _h2, _h3⟩ := hqmem
  have hc0 : q 0 = p 0 + ε / 2 := by simp [hq, frontier_e0]
  have hc1 : q 1 = p 1 := by simp [hq, frontier_e0]
  rw [hc0, hc1] at h1
  linarith

/-- Points on the second edge line are outside the interior. -/
theorem frontier_not_mem_of_f2 (p : plane) (h : 2 * p 0 - p 1 = 5) :
    p ∉ interior slantTriRegion := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hεpos, hεsub⟩ := hmem
  set q := p + (ε / 2) • frontier_e0 with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, frontier_dist_e0, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  have hqmem := hεsub hqball
  simp only [slantTriRegion, mem_ofPred_eq] at hqmem
  obtain ⟨_h1, h2, _h3⟩ := hqmem
  have hc0 : q 0 = p 0 + ε / 2 := by simp [hq, frontier_e0]
  have hc1 : q 1 = p 1 := by simp [hq, frontier_e0]
  rw [hc0, hc1] at h2
  linarith

/-- Points on the third edge line are outside the interior. -/
theorem frontier_not_mem_of_f3 (p : plane) (h : 3 * p 0 - 4 * p 1 = 0) :
    p ∉ interior slantTriRegion := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hεpos, hεsub⟩ := hmem
  set q := p + (ε / 2) • frontier_e1 with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, frontier_dist_e1, abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  have hqmem := hεsub hqball
  simp only [slantTriRegion, mem_ofPred_eq] at hqmem
  obtain ⟨_h1, _h2, h3⟩ := hqmem
  have hc0 : q 0 = p 0 := by simp [hq, frontier_e1]
  have hc1 : q 1 = p 1 + ε / 2 := by simp [hq, frontier_e1]
  rw [hc0, hc1] at h3
  linarith

/-- The interior of the closed triangle is the strict-inequality set. -/
theorem frontier_interior_eq : interior slantTriRegion = slantTriInterior := by
  apply Set.eq_of_subset_of_subset
  · intro p hmem
    have hsub : p ∈ slantTriRegion := interior_subset hmem
    simp only [slantTriRegion, mem_ofPred_eq] at hsub
    obtain ⟨hle1, hle2, hle3⟩ := hsub
    simp only [slantTriInterior, mem_ofPred_eq]
    have hf1 : p 0 - 3 * p 1 < 0 := by
      by_contra hcon
      have heq : p 0 - 3 * p 1 = 0 := by linarith
      exact frontier_not_mem_of_f1 p heq hmem
    have hf2 : 2 * p 0 - p 1 < 5 := by
      by_contra hcon
      have heq : 2 * p 0 - p 1 = 5 := by linarith
      exact frontier_not_mem_of_f2 p heq hmem
    have hf3 : (0:ℝ) < 3 * p 0 - 4 * p 1 := by
      by_contra hcon
      have heq : 3 * p 0 - 4 * p 1 = 0 := by linarith
      exact frontier_not_mem_of_f3 p heq hmem
    exact ⟨hf1, hf2, hf3⟩
  · have hmono := interior_mono frontier_subset_interior
    rw [IsOpen.interior_eq frontier_open_interiorSet] at hmono
    exact hmono

theorem frontier_cyclicEdges :
    cyclicEdges slantTriVerts = [(slA, slB), (slB, slC), (slC, slA)] := rfl

theorem frontier_boundary_unfold :
    boundarySet slantTriVerts =
      segment ℝ slA slB ∪ segment ℝ slB slC ∪ segment ℝ slC slA := by
  have h : boundarySet slantTriVerts =
      {p | ∃ e ∈ ([(slA, slB), (slB, slC), (slC, slA)] : List (plane × plane)),
        p ∈ segment ℝ e.1 e.2} := by
    unfold boundarySet
    rw [frontier_cyclicEdges]
  rw [h]
  ext p
  simp only [mem_ofPred_eq, mem_union, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨e, he, hp⟩
    rcases he with rfl | rfl | rfl
    · exact Or.inl (Or.inl hp)
    · exact Or.inl (Or.inr hp)
    · exact Or.inr hp
  · rintro ((h1 | h2) | h3)
    · exact ⟨(slA, slB), Or.inl rfl, h1⟩
    · exact ⟨(slB, slC), Or.inr (Or.inl rfl), h2⟩
    · exact ⟨(slC, slA), Or.inr (Or.inr rfl), h3⟩

/-- First side: the segment from `slA` to `slB`. -/
theorem frontier_seg_AB (p : plane) : p ∈ segment ℝ slA slB ↔
    p 0 - 3 * p 1 = 0 ∧ 2 * p 0 - p 1 ≤ 5 ∧ 0 ≤ 3 * p 0 - 4 * p 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    have h0 : (a • slA + b • slB) 0 = p 0 := by rw [h]
    have h1 : (a • slA + b • slB) 1 = p 1 := by rw [h]
    simp only [slA, slB] at h0 h1
    simp at h0 h1
    constructor
    · linarith
    · constructor <;> linarith
  · rintro ⟨heq, hle2, hle3⟩
    have hb0 : (0:ℝ) ≤ p 1 := by linarith
    have hb1 : p 1 ≤ 1 := by linarith
    refine ⟨1 - p 1, p 1, by linarith, hb0, by ring, ?_⟩
    ext i
    fin_cases i
    · have h0 : ((1 - p 1) • slA + (p 1) • slB) 0 = p 0 := by
        simp only [slA, slB]
        simp
        linarith
      exact h0
    · have h1 : ((1 - p 1) • slA + (p 1) • slB) 1 = p 1 := by
        simp only [slA, slB]
        simp
      exact h1

/-- Second side: the segment from `slB` to `slC`. -/
theorem frontier_seg_BC (p : plane) : p ∈ segment ℝ slB slC ↔
    p 0 - 3 * p 1 ≤ 0 ∧ 2 * p 0 - p 1 = 5 ∧ 0 ≤ 3 * p 0 - 4 * p 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    have h0 : (a • slB + b • slC) 0 = p 0 := by rw [h]
    have h1 : (a • slB + b • slC) 1 = p 1 := by rw [h]
    simp only [slB, slC] at h0 h1
    simp at h0 h1
    constructor
    · linarith
    · constructor
      · linarith
      · linarith
  · rintro ⟨hle1, heq, hle3⟩
    have hb0 : (0:ℝ) ≤ p 0 - 3 := by linarith
    have hb1 : p 0 - 3 ≤ 1 := by linarith
    refine ⟨1 - (p 0 - 3), p 0 - 3, by linarith, hb0, by ring, ?_⟩
    ext i
    fin_cases i
    · have h0 : ((1 - (p 0 - 3)) • slB + (p 0 - 3) • slC) 0 = p 0 := by
        simp only [slB, slC]
        simp
        ring
      exact h0
    · have h1 : ((1 - (p 0 - 3)) • slB + (p 0 - 3) • slC) 1 = p 1 := by
        simp only [slB, slC]
        simp
        linarith
      exact h1

/-- Third side: the segment from `slC` to `slA`. -/
theorem frontier_seg_CA (p : plane) : p ∈ segment ℝ slC slA ↔
    p 0 - 3 * p 1 ≤ 0 ∧ 2 * p 0 - p 1 ≤ 5 ∧ 3 * p 0 - 4 * p 1 = 0 := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, h⟩
    have h0 : (a • slC + b • slA) 0 = p 0 := by rw [h]
    have h1 : (a • slC + b • slA) 1 = p 1 := by rw [h]
    simp only [slC, slA] at h0 h1
    simp at h0 h1
    constructor
    · linarith
    · constructor
      · linarith
      · linarith
  · rintro ⟨hle1, hle2, heq⟩
    have hb0 : (0:ℝ) ≤ p 1 / 3 := by linarith
    have hb1 : p 1 / 3 ≤ 1 := by linarith
    refine ⟨p 1 / 3, 1 - p 1 / 3, hb0, by linarith, by ring, ?_⟩
    ext i
    fin_cases i
    · have h0 : ((p 1 / 3) • slC + (1 - p 1 / 3) • slA) 0 = p 0 := by
        simp only [slC, slA]
        simp
        linarith
      exact h0
    · have h1 : ((p 1 / 3) • slC + (1 - p 1 / 3) • slA) 1 = p 1 := by
        simp only [slC, slA]
        simp
      exact h1

/-- Stage-2 coupling: the frontier of the explicit slanted triangle is its
boundary chain. -/
theorem frontier_slantTriRegion :
    frontier slantTriRegion = boundarySet slantTriVerts := by
  rw [IsClosed.frontier_eq frontier_closed_region, frontier_interior_eq,
    frontier_boundary_unfold]
  ext p
  simp only [slantTriRegion, slantTriInterior, mem_ofPred_eq, mem_sdiff, mem_union]
  constructor
  · rintro ⟨⟨hle1, hle2, hle3⟩, hnot⟩
    have hdisj : p 0 - 3 * p 1 = 0 ∨ 2 * p 0 - p 1 = 5 ∨ 3 * p 0 - 4 * p 1 = 0 := by
      by_contra hcon
      have hne1 : p 0 - 3 * p 1 ≠ 0 := fun heq => hcon (Or.inl heq)
      have hne2 : 2 * p 0 - p 1 ≠ 5 := fun heq => hcon (Or.inr (Or.inl heq))
      have hne3 : 3 * p 0 - 4 * p 1 ≠ 0 := fun heq => hcon (Or.inr (Or.inr heq))
      have hf1 : p 0 - 3 * p 1 < 0 := lt_of_le_of_ne hle1 hne1
      have hf2 : 2 * p 0 - p 1 < 5 := lt_of_le_of_ne hle2 hne2
      have hf3 : (0:ℝ) < 3 * p 0 - 4 * p 1 := lt_of_le_of_ne' hle3 hne3
      exact hnot ⟨hf1, hf2, hf3⟩
    rcases hdisj with heq1 | heq2 | heq3
    · have hmem : p ∈ segment ℝ slA slB := (frontier_seg_AB p).mpr ⟨heq1, hle2, hle3⟩
      exact Or.inl (Or.inl hmem)
    · have hmem : p ∈ segment ℝ slB slC := (frontier_seg_BC p).mpr ⟨hle1, heq2, hle3⟩
      exact Or.inl (Or.inr hmem)
    · have hmem : p ∈ segment ℝ slC slA := (frontier_seg_CA p).mpr ⟨hle1, hle2, heq3⟩
      exact Or.inr hmem
  · rintro ((hAB | hBC) | hCA)
    · obtain ⟨heq1, hle2, hle3⟩ := (frontier_seg_AB p).mp hAB
      refine ⟨⟨le_of_eq heq1, hle2, hle3⟩, ?_⟩
      rintro ⟨hf1, _hf2, _hf3⟩
      linarith
    · obtain ⟨hle1, heq2, hle3⟩ := (frontier_seg_BC p).mp hBC
      refine ⟨⟨hle1, le_of_eq heq2, hle3⟩, ?_⟩
      rintro ⟨_hf1, hf2, _hf3⟩
      linarith
    · obtain ⟨hle1, hle2, heq3⟩ := (frontier_seg_CA p).mp hCA
      refine ⟨⟨hle1, hle2, le_of_eq heq3.symm⟩, ?_⟩
      rintro ⟨_hf1, _hf2, hf3⟩
      linarith

/-- The slanted triangle as a `Poly` instance. -/
def slantTriPoly : Poly :=
  { vertices := slantTriVerts
    len_ge := len_ge_slantTriVerts
    region := slantTriRegion
    boundary_eq := frontier_slantTriRegion
    closed_region := isClosed_slantTriRegion
    bounded := isBounded_slantTriRegion
    interior_nonempty := interiorNonempty_slantTriRegion
    simple := simple_slantTriVerts }

/-- The hole-free workspace over the slanted triangle. -/
def slantTriWorkspace : Workspace :=
  { outer := slantTriPoly
    holes := []
    hole_inside := by simp
    holes_disjoint := List.Pairwise.nil }

/-- The interior point lies in the strict set (direct computation). -/
theorem frontier_interiorPoint_mem : triInteriorPoint ∈ slantTriInterior := by
  simp only [triInteriorPoint, slantTriInterior, mem_ofPred_eq]
  simp
  norm_num

/-- The interior point lies in the region interior. -/
theorem frontier_interiorPoint_mem_interior :
    triInteriorPoint ∈ interior slantTriRegion := by
  rw [frontier_interior_eq]
  exact frontier_interiorPoint_mem

/-- Free space contains the interior point. -/
example : triInteriorPoint ∈ slantTriWorkspace.freeSpace := by
  have hmem : triInteriorPoint ∈ interior slantTriPoly.region :=
    frontier_interiorPoint_mem_interior
  have hnil : holeUnion ([] : List Poly) = ∅ := rfl
  simp only [Workspace.freeSpace, slantTriWorkspace, slantTriPoly] at ⊢
  rw [hnil]
  simp only [mem_sdiff, mem_empty_iff_false, not_false_eq_true, and_true]
  exact hmem

/-- Free space excludes a concrete exterior point. -/
example : (!₂[5, 0] : plane) ∉ slantTriWorkspace.freeSpace := by
  intro hmem
  simp only [Workspace.freeSpace, slantTriWorkspace, slantTriPoly] at hmem
  have hnil : holeUnion ([] : List Poly) = ∅ := rfl
  rw [hnil] at hmem
  simp only [mem_sdiff, mem_empty_iff_false, not_false_eq_true, and_true] at hmem
  rw [frontier_interior_eq] at hmem
  simp only [slantTriInterior, mem_ofPred_eq] at hmem
  simp at hmem

/-- Vertex count is 3. -/
example : slantTriWorkspace.vertexCount = 3 := rfl

/-- General position holds. -/
example : slantTriWorkspace.GeneralPosition := by
  simp only [Workspace.GeneralPosition, Workspace.allVertices, slantTriWorkspace, slantTriPoly]
  simp only [List.map_nil, List.flatten_nil, List.append_nil]
  unfold generalPositionOf xCoordsOf slantTriVerts
  simp only [List.map_cons, List.map_nil]
  simp only [slA, slB, slC]
  simp

#print axioms frontier_slantTriRegion
#print axioms slantTriWorkspace

end Cslib.Planning.MotionPlanning.PolygonalWorkspace
