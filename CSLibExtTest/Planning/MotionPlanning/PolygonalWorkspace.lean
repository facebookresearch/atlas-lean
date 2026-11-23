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
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

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
/-- Bow-tie vertex points: `(0,0)`, `(2,2)`, `(0,2)`, `(2,0)`. -/
def bowA : plane := !₂[0, 0]
def bowB : plane := !₂[2, 2]
def bowC : plane := !₂[0, 2]
def bowD : plane := !₂[2, 0]
/-- The bow-tie vertex list `[(0,0),(2,2),(0,2),(2,0)]`. -/
def bowVerts : List plane := [bowA, bowB, bowC, bowD]

theorem bowA_x : bowA 0 = 0 := by simp [bowA]
theorem bowA_y : bowA 1 = 0 := by simp [bowA]
theorem bowB_x : bowB 0 = 2 := by simp [bowB]
theorem bowB_y : bowB 1 = 2 := by simp [bowB]
theorem bowC_x : bowC 0 = 0 := by simp [bowC]
theorem bowC_y : bowC 1 = 2 := by simp [bowC]
theorem bowD_x : bowD 0 = 2 := by simp [bowD]
theorem bowD_y : bowD 1 = 0 := by simp [bowD]

theorem bowA_ne_bowB : bowA ≠ bowB := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [bowA_x, bowB_x] at h0
  norm_num at h0

theorem bowA_ne_bowC : bowA ≠ bowC := by
  intro h
  have h1 := congrArg (fun q : plane => q 1) h
  rw [bowA_y, bowC_y] at h1
  norm_num at h1

theorem bowA_ne_bowD : bowA ≠ bowD := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [bowA_x, bowD_x] at h0
  norm_num at h0

theorem bowB_ne_bowC : bowB ≠ bowC := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [bowB_x, bowC_x] at h0
  norm_num at h0

theorem bowB_ne_bowD : bowB ≠ bowD := by
  intro h
  have h1 := congrArg (fun q : plane => q 1) h
  rw [bowB_y, bowD_y] at h1
  norm_num at h1

theorem bowC_ne_bowD : bowC ≠ bowD := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [bowC_x, bowD_x] at h0
  norm_num at h0

theorem nodup_bowVerts : List.Nodup bowVerts := by
  have hvs : bowVerts = [bowA, bowB, bowC, bowD] := rfl
  rw [hvs, List.nodup_cons, List.nodup_cons, List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ?_, ?_, ?_, List.nodup_nil⟩
  · simp [bowA_ne_bowB, bowA_ne_bowC, bowA_ne_bowD]
  · simp [bowB_ne_bowC, bowB_ne_bowD]
  · simp [bowC_ne_bowD]
  · simp

theorem cyclicEdges_bowVerts :
    cyclicEdges bowVerts = [(bowA, bowB), (bowB, bowC), (bowC, bowD), (bowD, bowA)] := rfl

theorem noZero_bowVerts : ∀ e ∈ cyclicEdges bowVerts, e.1 ≠ e.2 := by
  intro e he
  rw [cyclicEdges_bowVerts] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · show bowA ≠ bowB
    exact bowA_ne_bowB
  · show bowB ≠ bowC
    exact bowB_ne_bowC
  · show bowC ≠ bowD
    exact bowC_ne_bowD
  · show bowD ≠ bowA
    exact Ne.symm bowA_ne_bowD

/-- The crossing point `(1,1)` of the two bow-tie diagonals. -/
def bowMid : plane := !₂[1, 1]

theorem bowMid_mem_AB : bowMid ∈ segment ℝ bowA bowB := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  fin_cases i <;> simp [bowA, bowB, bowMid]

theorem bowMid_mem_CD : bowMid ∈ segment ℝ bowC bowD := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  fin_cases i <;> simp [bowC, bowD, bowMid]

theorem len_bowVerts : (cyclicEdges bowVerts).length = 4 := rfl

/-- The bow-tie violates occurrence disjointness at the non-adjacent pair `(0,2)`. -/
theorem not_simple_bowVerts : ¬ PolySimple bowVerts := by
  rintro ⟨-, -, -, hadj⟩
  have h0 := hadj 0 2 (by decide) (by decide) (by decide)
  have hnadj : ¬ edgeAdjacent 0 2 (cyclicEdges bowVerts).length := by
    rw [len_bowVerts]
    unfold edgeAdjacent
    decide
  have hdisj : Disjoint (segment ℝ bowA bowB) (segment ℝ bowC bowD) := h0.2 hnadj
  exact (Set.disjoint_left.mp hdisj bowMid_mem_AB) bowMid_mem_CD

/-- Adjacent-overlap vertex points: `(0,0)`, `(2,0)`, `(1,0)`, `(1,1)`. -/
def ovA : plane := !₂[0, 0]
def ovB : plane := !₂[2, 0]
def ovC : plane := !₂[1, 0]
def ovD : plane := !₂[1, 1]
/-- The adjacent-overlap vertex list `[(0,0),(2,0),(1,0),(1,1)]`. -/
def ovVerts : List plane := [ovA, ovB, ovC, ovD]

theorem ovA_x : ovA 0 = 0 := by simp [ovA]
theorem ovB_x : ovB 0 = 2 := by simp [ovB]
theorem ovC_x : ovC 0 = 1 := by simp [ovC]
theorem ovC_y : ovC 1 = 0 := by simp [ovC]
theorem ovD_x : ovD 0 = 1 := by simp [ovD]
theorem ovD_y : ovD 1 = 1 := by simp [ovD]

theorem ovA_ne_ovB : ovA ≠ ovB := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [ovA_x, ovB_x] at h0
  norm_num at h0

theorem ovA_ne_ovC : ovA ≠ ovC := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [ovA_x, ovC_x] at h0
  norm_num at h0

theorem ovA_ne_ovD : ovA ≠ ovD := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [ovA_x, ovD_x] at h0
  norm_num at h0

theorem ovB_ne_ovC : ovB ≠ ovC := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [ovB_x, ovC_x] at h0
  norm_num at h0

theorem ovB_ne_ovD : ovB ≠ ovD := by
  intro h
  have h0 := congrArg (fun q : plane => q 0) h
  rw [ovB_x, ovD_x] at h0
  norm_num at h0

theorem ovC_ne_ovD : ovC ≠ ovD := by
  intro h
  have h1 := congrArg (fun q : plane => q 1) h
  rw [ovC_y, ovD_y] at h1
  norm_num at h1

theorem nodup_ovVerts : List.Nodup ovVerts := by
  have hvs : ovVerts = [ovA, ovB, ovC, ovD] := rfl
  rw [hvs, List.nodup_cons, List.nodup_cons, List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ?_, ?_, ?_, List.nodup_nil⟩
  · simp [ovA_ne_ovB, ovA_ne_ovC, ovA_ne_ovD]
  · simp [ovB_ne_ovC, ovB_ne_ovD]
  · simp [ovC_ne_ovD]
  · simp

theorem cyclicEdges_ovVerts :
    cyclicEdges ovVerts = [(ovA, ovB), (ovB, ovC), (ovC, ovD), (ovD, ovA)] := rfl

theorem noZero_ovVerts : ∀ e ∈ cyclicEdges ovVerts, e.1 ≠ e.2 := by
  intro e he
  rw [cyclicEdges_ovVerts] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · show ovA ≠ ovB
    exact ovA_ne_ovB
  · show ovB ≠ ovC
    exact ovB_ne_ovC
  · show ovC ≠ ovD
    exact ovC_ne_ovD
  · show ovD ≠ ovA
    exact Ne.symm ovA_ne_ovD

/-- The point `(3/2,0)`, interior to both overlapping adjacent segments. -/
noncomputable def ovMid : plane := !₂[3 / 2, 0]

theorem ovMid_x : ovMid 0 = 3 / 2 := by simp [ovMid]

theorem ovMid_mem_AB : ovMid ∈ segment ℝ ovA ovB := by
  refine ⟨1 / 4, 3 / 4, by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  fin_cases i <;> simp [ovA, ovB, ovMid]; norm_num

theorem ovMid_mem_BC : ovMid ∈ segment ℝ ovB ovC := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  fin_cases i <;> simp [ovB, ovC, ovMid]; norm_num

theorem len_ovVerts : (cyclicEdges ovVerts).length = 4 := rfl

/-- The overlap violates the adjacent-singleton condition at occurrences `(0,1)`. -/
theorem not_simple_ovVerts : ¬ PolySimple ovVerts := by
  rintro ⟨-, -, -, hadj⟩
  have h0 := hadj 0 1 (by decide) (by decide) (by decide)
  have hadj01 : edgeAdjacent 0 1 (cyclicEdges ovVerts).length := by
    rw [len_ovVerts]
    unfold edgeAdjacent
    decide
  have hsing : ∃ p ∈ ((({ovA, ovB} : Set plane) ∩ ({ovB, ovC} : Set plane))),
      (segment ℝ ovA ovB ∩ segment ℝ ovB ovC : Set plane) = {p} := h0.1 hadj01
  obtain ⟨p, -, hinter⟩ := hsing
  have hB : ovB ∈ ({p} : Set plane) := by
    rw [← hinter]
    exact Set.mem_inter (right_mem_segment ℝ ovA ovB) (left_mem_segment ℝ ovB ovC)
  have hM : ovMid ∈ ({p} : Set plane) := by
    rw [← hinter]
    exact Set.mem_inter ovMid_mem_AB ovMid_mem_BC
  have hBeq : ovB = p := Set.mem_singleton_iff.mp hB
  have hMeq : ovMid = p := Set.mem_singleton_iff.mp hM
  have hcontra : ovB = ovMid := hBeq.trans hMeq.symm
  have h0c := congrArg (fun q : plane => q 0) hcontra
  rw [ovB_x, ovMid_x] at h0c
  norm_num at h0c

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
  · have hmono := interior_mono slantTriInterior_subset_region
    rw [IsOpen.interior_eq isOpen_slantTriInterior] at hmono
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
  rw [IsClosed.frontier_eq isClosed_slantTriRegion, frontier_interior_eq,
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

/-- The interior point lies in the region interior. -/
theorem frontier_interiorPoint_mem_interior :
    triInteriorPoint ∈ interior slantTriRegion := by
  rw [frontier_interior_eq]
  exact interiorPoint_mem_slantTriInterior

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

/-!
One-hole workspace fixture over the slanted triangle.

The hole is the inner triangle obtained by tightening each outer half-plane
by margin 1. For polygonal configuration-space obstacles see LaValle,
Planning Algorithms, Sec. 6.2.1.

These declarations live in the CSLibExtTest PolygonalWorkspace module
after the slanted-triangle frontier fixtures, whose continuity and
witness-direction lemmas they reuse.
-/

/-! Hole region, interior, and vertices. -/

def holeRegion : Set plane :=
  {p | p 0 - 3 * p 1 ≤ -1 ∧ 2 * p 0 - p 1 ≤ 4 ∧ 1 ≤ 3 * p 0 - 4 * p 1}

def holeInterior : Set plane :=
  {p | p 0 - 3 * p 1 < -1 ∧ 2 * p 0 - p 1 < 4 ∧ 1 < 3 * p 0 - 4 * p 1}

noncomputable def holeCenter : plane := !₂[(12 / 5 : ℝ), (4 / 3 : ℝ)]

noncomputable def hA : plane := !₂[(7 / 5 : ℝ), (4 / 5 : ℝ)]
noncomputable def hB : plane := !₂[(13 / 5 : ℝ), (6 / 5 : ℝ)]
def hC : plane := !₂[(3 : ℝ), (2 : ℝ)]
noncomputable def holeVerts : List plane := [hA, hB, hC]

/-! Coordinate continuity helpers. -/

theorem coord0_cont : Continuous (fun p : plane => p 0) :=
  PiLp.continuous_apply 2 _ 0
theorem coord1_cont : Continuous (fun p : plane => p 1) :=
  PiLp.continuous_apply 2 _ 1

/-! Fixture lemmas mirroring the outer triangle. -/

theorem isClosed_holeRegion : IsClosed holeRegion := by
  unfold holeRegion
  exact (isClosed_le frontier_cont_f1 continuous_const).inter
    ((isClosed_le frontier_cont_f2 continuous_const).inter
      (isClosed_le continuous_const frontier_cont_f3))

theorem isBounded_holeRegion : Bornology.IsBounded holeRegion := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : plane)]
  refine ⟨8, ?_⟩
  intro p hp
  simp only [holeRegion, Set.mem_ofPred_eq] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have b0 : |p 0| ≤ 5 := by
    rw [abs_le]
    constructor <;> linarith
  have b1 : |p 1| ≤ 5 := by
    rw [abs_le]
    constructor <;> linarith
  have s0 : (p 0) ^ 2 ≤ 25 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp b0
    have h := sq_le_sq' hlo hhi
    norm_num at h ⊢
    linarith
  have s1 : (p 1) ^ 2 ≤ 25 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp b1
    have h := sq_le_sq' hlo hhi
    norm_num at h ⊢
    linarith
  have hnorm : ‖p‖ ≤ 8 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : (∑ i, ‖p.ofLp i‖ ^ 2) = (p 0) ^ 2 + (p 1) ^ 2 := by
      rw [Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hsum]
    have hb : (p 0) ^ 2 + (p 1) ^ 2 ≤ 64 := by linarith
    calc √( (p 0) ^ 2 + (p 1) ^ 2 ) ≤ √(64 : ℝ) := Real.sqrt_le_sqrt hb
      _ = 8 := by norm_num
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hnorm

theorem holeCenter_mem : holeCenter ∈ holeInterior := by
  simp only [holeCenter, holeInterior, Set.mem_ofPred_eq]
  norm_num

theorem isOpen_holeInterior : IsOpen holeInterior := by
  unfold holeInterior
  exact (isOpen_lt frontier_cont_f1 continuous_const).inter
    ((isOpen_lt frontier_cont_f2 continuous_const).inter
      (isOpen_lt continuous_const frontier_cont_f3))

theorem holeInterior_subset : holeInterior ⊆ holeRegion := by
  intro p hp
  simp only [holeInterior, holeRegion, Set.mem_ofPred_eq] at hp ⊢
  obtain ⟨a, b, c⟩ := hp
  exact ⟨le_of_lt a, le_of_lt b, le_of_lt c⟩

theorem interiorNonempty_holeRegion : (interior holeRegion).Nonempty :=
  ⟨holeCenter, interior_maximal holeInterior_subset isOpen_holeInterior holeCenter_mem⟩

theorem hAB_ne : hA ≠ hB := by
  intro h
  have hc := congrArg (fun p : plane => p 0) h
  norm_num [hA, hB] at hc
theorem hAC_ne : hA ≠ hC := by
  intro h
  have hc := congrArg (fun p : plane => p 0) h
  norm_num [hA, hC] at hc
theorem hBC_ne : hB ≠ hC := by
  intro h
  have hc := congrArg (fun p : plane => p 0) h
  norm_num [hB, hC] at hc
theorem hCA_ne : hC ≠ hA := fun h => hAC_ne h.symm

theorem nodup_holeVerts : List.Nodup holeVerts := by
  simp [holeVerts, List.nodup_cons, hAB_ne, hAC_ne, hBC_ne]

theorem len_ge_holeVerts : 3 ≤ holeVerts.length := by
  simp [holeVerts]

theorem cyclicEdges_holeVerts :
    cyclicEdges holeVerts = [(hA, hB), (hB, hC), (hC, hA)] := by
  rfl

theorem noZero_holeVerts : ∀ e ∈ cyclicEdges holeVerts, e.1 ≠ e.2 := by
  intro e he
  rw [cyclicEdges_holeVerts] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact hAB_ne
  · exact hBC_ne
  · exact hCA_ne

/-! Side lines through hole vertices, for occurrence and frontier proofs. -/

def L1 : Set plane := {p | p 0 - 3 * p 1 = -1}
def L2 : Set plane := {p | 2 * p 0 - p 1 = 4}
def L3 : Set plane := {p | 3 * p 0 - 4 * p 1 = 1}

theorem convex_L1 : Convex ℝ L1 := by
  intro x hx y hy a b ha hb hab
  simp only [L1, Set.mem_ofPred_eq] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ⊢
  have h : (a * x 0 + b * y 0) - 3 * (a * x 1 + b * y 1)
      = a * (x 0 - 3 * x 1) + b * (y 0 - 3 * y 1) := by ring
  rw [h, hx, hy]
  linarith

theorem convex_L2 : Convex ℝ L2 := by
  intro x hx y hy a b ha hb hab
  simp only [L2, Set.mem_ofPred_eq] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ⊢
  have h : 2 * (a * x 0 + b * y 0) - (a * x 1 + b * y 1)
      = a * (2 * x 0 - x 1) + b * (2 * y 0 - y 1) := by ring
  rw [h, hx, hy]
  linarith

theorem convex_L3 : Convex ℝ L3 := by
  intro x hx y hy a b ha hb hab
  simp only [L3, Set.mem_ofPred_eq] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ⊢
  have h : 3 * (a * x 0 + b * y 0) - 4 * (a * x 1 + b * y 1)
      = a * (3 * x 0 - 4 * x 1) + b * (3 * y 0 - 4 * y 1) := by ring
  rw [h, hx, hy]
  linarith

theorem hA_L1 : hA ∈ L1 := by simp [hA, L1]; norm_num
theorem hB_L1 : hB ∈ L1 := by simp [hB, L1]; norm_num
theorem hB_L2 : hB ∈ L2 := by simp [hB, L2]; norm_num
theorem hC_L2 : hC ∈ L2 := by simp [hC, L2]; norm_num
theorem hC_L3 : hC ∈ L3 := by simp [hC, L3]; norm_num
theorem hA_L3 : hA ∈ L3 := by simp [hA, L3]; norm_num

theorem seg_AB_sub_L1 : segment ℝ hA hB ⊆ L1 :=
  convex_L1.segment_subset hA_L1 hB_L1
theorem seg_BC_sub_L2 : segment ℝ hB hC ⊆ L2 :=
  convex_L2.segment_subset hB_L2 hC_L2
theorem seg_CA_sub_L3 : segment ℝ hC hA ⊆ L3 :=
  convex_L3.segment_subset hC_L3 hA_L3

theorem point_eq_hB_of_lines (p : plane)
    (l1 : p 0 - 3 * p 1 = -1) (l2 : 2 * p 0 - p 1 = 4) : p = hB := by
  have e0 : p 0 = 13 / 5 := by linarith
  have e1 : p 1 = 6 / 5 := by linarith
  have hb0 : hB 0 = 13 / 5 := by simp [hB]
  have hb1 : hB 1 = 6 / 5 := by simp [hB]
  apply PiLp.ext
  intro i
  fin_cases i
  · simp only [Fin.mk_zero]
    rw [e0, hb0]
  · simp only [Fin.mk_one]
    rw [e1, hb1]

theorem point_eq_hA_of_lines (p : plane)
    (l1 : p 0 - 3 * p 1 = -1) (l3 : 3 * p 0 - 4 * p 1 = 1) : p = hA := by
  have e0 : p 0 = 7 / 5 := by linarith
  have e1 : p 1 = 4 / 5 := by linarith
  have ha0 : hA 0 = 7 / 5 := by simp [hA]
  have ha1 : hA 1 = 4 / 5 := by simp [hA]
  apply PiLp.ext
  intro i
  fin_cases i
  · simp only [Fin.mk_zero]
    rw [e0, ha0]
  · simp only [Fin.mk_one]
    rw [e1, ha1]

theorem point_eq_hC_of_lines (p : plane)
    (l2 : 2 * p 0 - p 1 = 4) (l3 : 3 * p 0 - 4 * p 1 = 1) : p = hC := by
  have e0 : p 0 = 3 := by linarith
  have e1 : p 1 = 2 := by linarith
  have hc0 : hC 0 = 3 := by simp [hC]
  have hc1 : hC 1 = 2 := by simp [hC]
  apply PiLp.ext
  intro i
  fin_cases i
  · simp only [Fin.mk_zero]
    rw [e0, hc0]
  · simp only [Fin.mk_one]
    rw [e1, hc1]

theorem seg_inter_AB_BC : segment ℝ hA hB ∩ segment ℝ hB hC = {hB} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · exact ⟨right_mem_segment ℝ hA hB, left_mem_segment ℝ hB hC⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have q1 := seg_AB_sub_L1 hp1
    have q2 := seg_BC_sub_L2 hp2
    simp only [L1, L2, Set.mem_ofPred_eq] at q1 q2
    exact point_eq_hB_of_lines p q1 q2

theorem seg_inter_AB_CA : segment ℝ hA hB ∩ segment ℝ hC hA = {hA} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · exact ⟨left_mem_segment ℝ hA hB, right_mem_segment ℝ hC hA⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have q1 := seg_AB_sub_L1 hp1
    have q3 := seg_CA_sub_L3 hp2
    simp only [L1, L3, Set.mem_ofPred_eq] at q1 q3
    exact point_eq_hA_of_lines p q1 q3

theorem seg_inter_BC_CA : segment ℝ hB hC ∩ segment ℝ hC hA = {hC} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · exact ⟨right_mem_segment ℝ hB hC, left_mem_segment ℝ hC hA⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have q2 := seg_BC_sub_L2 hp1
    have q3 := seg_CA_sub_L3 hp2
    simp only [L2, L3, Set.mem_ofPred_eq] at q2 q3
    exact point_eq_hC_of_lines p q2 q3

theorem simple_holeVerts : PolySimple holeVerts := by
  refine ⟨len_ge_holeVerts, nodup_holeVerts, noZero_holeVerts, ?_⟩
  intro i j hi hj hne
  have hi3 : i < 3 := hi
  have hj3 : j < 3 := hj
  interval_cases i <;> interval_cases j
  · exact absurd rfl hne
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({hA, hB} : Set plane) ∩ ({hB, hC} : Set plane)),
        (segment ℝ hA hB ∩ segment ℝ hB hC : Set plane) = {p}
      exact ⟨hB, by simp, seg_inter_AB_BC⟩
    · show edgeAdjacent 0 1 3
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({hA, hB} : Set plane) ∩ ({hC, hA} : Set plane)),
        (segment ℝ hA hB ∩ segment ℝ hC hA : Set plane) = {p}
      exact ⟨hA, by simp, seg_inter_AB_CA⟩
    · show edgeAdjacent 0 2 3
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({hB, hC} : Set plane) ∩ ({hA, hB} : Set plane)),
        (segment ℝ hB hC ∩ segment ℝ hA hB : Set plane) = {p}
      refine ⟨hB, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_inter_AB_BC
    · show edgeAdjacent 1 0 3
      unfold edgeAdjacent
      decide
  · exact absurd rfl hne
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({hB, hC} : Set plane) ∩ ({hC, hA} : Set plane)),
        (segment ℝ hB hC ∩ segment ℝ hC hA : Set plane) = {p}
      exact ⟨hC, by simp, seg_inter_BC_CA⟩
    · show edgeAdjacent 1 2 3
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({hC, hA} : Set plane) ∩ ({hA, hB} : Set plane)),
        (segment ℝ hC hA ∩ segment ℝ hA hB : Set plane) = {p}
      refine ⟨hA, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_inter_AB_CA
    · show edgeAdjacent 2 0 3
      unfold edgeAdjacent
      decide
  · refine ⟨fun _ => ?_, fun h => absurd ?_ h⟩
    · show ∃ p ∈ (({hC, hA} : Set plane) ∩ ({hB, hC} : Set plane)),
        (segment ℝ hC hA ∩ segment ℝ hB hC : Set plane) = {p}
      refine ⟨hC, by simp, ?_⟩
      rw [Set.inter_comm]
      exact seg_inter_BC_CA
    · show edgeAdjacent 2 1 3
      unfold edgeAdjacent
      decide
  · exact absurd rfl hne

/-! Interior characterization via outward witnesses. -/

def d3 : plane := !₂[(-1 : ℝ), (0 : ℝ)]
theorem norm_d3 : ‖d3‖ = 1 := by
  simp [d3, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem not_interior_of_L1_eq (p : plane)
    (heq : p 0 - 3 * p 1 = -1) : p ∉ interior holeRegion := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hεpos, hball⟩ := hmem
  set q := p + (ε / 2) • frontier_e0 with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : q - p = (ε / 2) • frontier_e0 := by simp [hq]
    rw [hsub, norm_smul, Real.norm_eq_abs, frontier_e0_norm, mul_one]
    rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  have hqout : q ∉ holeRegion := by
    simp only [holeRegion, Set.mem_ofPred_eq]
    intro h
    obtain ⟨h1, _h2, _h3⟩ := h
    have e0 : q 0 = p 0 + ε / 2 := by
      simp [hq, PiLp.add_apply, PiLp.smul_apply, frontier_e0]
    have e1 : q 1 = p 1 := by
      simp [hq, PiLp.add_apply, PiLp.smul_apply, frontier_e0]
    rw [e0, e1] at h1
    linarith
  exact hqout (hball hqball)

theorem not_interior_of_L2_eq (p : plane)
    (heq : 2 * p 0 - p 1 = 4) : p ∉ interior holeRegion := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hεpos, hball⟩ := hmem
  set q := p + (ε / 2) • frontier_e0 with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : q - p = (ε / 2) • frontier_e0 := by simp [hq]
    rw [hsub, norm_smul, Real.norm_eq_abs, frontier_e0_norm, mul_one]
    rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  have hqout : q ∉ holeRegion := by
    simp only [holeRegion, Set.mem_ofPred_eq]
    intro h
    obtain ⟨_h1, h2, _h3⟩ := h
    have e0 : q 0 = p 0 + ε / 2 := by
      simp [hq, PiLp.add_apply, PiLp.smul_apply, frontier_e0]
    have e1 : q 1 = p 1 := by
      simp [hq, PiLp.add_apply, PiLp.smul_apply, frontier_e0]
    rw [e0, e1] at h2
    linarith
  exact hqout (hball hqball)

theorem not_interior_of_L3_eq (p : plane)
    (heq : 3 * p 0 - 4 * p 1 = 1) : p ∉ interior holeRegion := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hεpos, hball⟩ := hmem
  set q := p + (ε / 2) • d3 with hq
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : q - p = (ε / 2) • d3 := by simp [hq]
    rw [hsub, norm_smul, Real.norm_eq_abs, norm_d3, mul_one]
    rw [abs_of_pos (by linarith : (0:ℝ) < ε / 2)]
    linarith
  have hqout : q ∉ holeRegion := by
    simp only [holeRegion, Set.mem_ofPred_eq]
    intro h
    obtain ⟨_h1, _h2, h3⟩ := h
    have e0 : q 0 = p 0 - ε / 2 := by
      simp [hq, PiLp.add_apply, PiLp.smul_apply, d3]
      ring
    have e1 : q 1 = p 1 := by
      simp [hq, PiLp.add_apply, PiLp.smul_apply, d3]
    rw [e0, e1] at h3
    linarith
  exact hqout (hball hqball)

theorem interior_holeRegion_eq : interior holeRegion = holeInterior := by
  apply Set.Subset.antisymm
  · intro p hp
    have hmem : p ∈ holeRegion := interior_subset hp
    simp only [holeRegion, Set.mem_ofPred_eq] at hmem
    simp only [holeInterior, Set.mem_ofPred_eq]
    obtain ⟨h1, h2, h3⟩ := hmem
    refine ⟨?_, ?_, ?_⟩
    · rcases lt_or_eq_of_le h1 with hlt | heq
      · exact hlt
      · exact absurd hp (not_interior_of_L1_eq p heq)
    · rcases lt_or_eq_of_le h2 with hlt | heq
      · exact hlt
      · exact absurd hp (not_interior_of_L2_eq p heq)
    · rcases lt_or_eq_of_le h3 with hlt | heq
      · exact hlt
      · exact absurd hp (not_interior_of_L3_eq p heq.symm)
  · exact interior_maximal holeInterior_subset isOpen_holeInterior

/-! Convexity of the hole region and side inclusions. -/

def H1 : Set plane := {p | p 0 - 3 * p 1 ≤ -1}
def H2 : Set plane := {p | 2 * p 0 - p 1 ≤ 4}
def H3 : Set plane := {p | 1 ≤ 3 * p 0 - 4 * p 1}

theorem convex_H1 : Convex ℝ H1 := by
  intro x hx y hy a b ha hb hab
  simp only [H1, Set.mem_ofPred_eq] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ⊢
  have h : (a * x 0 + b * y 0) - 3 * (a * x 1 + b * y 1)
      = a * (x 0 - 3 * x 1) + b * (y 0 - 3 * y 1) := by ring
  rw [h]
  have i1 : a * (x 0 - 3 * x 1) ≤ a * (-1) := mul_le_mul_of_nonneg_left hx ha
  have i2 : b * (y 0 - 3 * y 1) ≤ b * (-1) := mul_le_mul_of_nonneg_left hy hb
  have i3 : a * (x 0 - 3 * x 1) + b * (y 0 - 3 * y 1) ≤ a * (-1) + b * (-1) :=
    add_le_add i1 i2
  have i4 : a * (-1 : ℝ) + b * (-1) = -1 := by
    have h4 : a * (-1 : ℝ) + b * (-1) = -(a + b) := by ring
    rw [h4, hab]
  linarith

theorem convex_H2 : Convex ℝ H2 := by
  intro x hx y hy a b ha hb hab
  simp only [H2, Set.mem_ofPred_eq] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ⊢
  have h : 2 * (a * x 0 + b * y 0) - (a * x 1 + b * y 1)
      = a * (2 * x 0 - x 1) + b * (2 * y 0 - y 1) := by ring
  rw [h]
  have i1 : a * (2 * x 0 - x 1) ≤ a * 4 := mul_le_mul_of_nonneg_left hx ha
  have i2 : b * (2 * y 0 - y 1) ≤ b * 4 := mul_le_mul_of_nonneg_left hy hb
  have i3 : a * (2 * x 0 - x 1) + b * (2 * y 0 - y 1) ≤ a * 4 + b * 4 :=
    add_le_add i1 i2
  have i4 : a * (4 : ℝ) + b * 4 = 4 := by
    have h4 : a * (4 : ℝ) + b * 4 = (a + b) * 4 := by ring
    rw [h4, hab]
    norm_num
  linarith

theorem convex_H3 : Convex ℝ H3 := by
  intro x hx y hy a b ha hb hab
  simp only [H3, Set.mem_ofPred_eq] at hx hy ⊢
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ⊢
  have h : 3 * (a * x 0 + b * y 0) - 4 * (a * x 1 + b * y 1)
      = a * (3 * x 0 - 4 * x 1) + b * (3 * y 0 - 4 * y 1) := by ring
  rw [h]
  have i1 : a * (1 : ℝ) ≤ a * (3 * x 0 - 4 * x 1) := mul_le_mul_of_nonneg_left hx ha
  have i2 : b * (1 : ℝ) ≤ b * (3 * y 0 - 4 * y 1) := mul_le_mul_of_nonneg_left hy hb
  have i3 : a * (1 : ℝ) + b * 1 ≤ a * (3 * x 0 - 4 * x 1) + b * (3 * y 0 - 4 * y 1) :=
    add_le_add i1 i2
  have i4 : a * (1 : ℝ) + b * 1 = 1 := by
    have h4 : a * (1 : ℝ) + b * 1 = a + b := by ring
    rw [h4, hab]
  linarith

theorem holeRegion_eq_inter : holeRegion = H1 ∩ (H2 ∩ H3) := by
  ext p
  simp [holeRegion, H1, H2, H3]

theorem convex_holeRegion : Convex ℝ holeRegion := by
  rw [holeRegion_eq_inter]
  exact convex_H1.inter (convex_H2.inter convex_H3)

theorem hA_mem_hole : hA ∈ holeRegion := by
  simp only [holeRegion, Set.mem_ofPred_eq, hA]
  norm_num
theorem hB_mem_hole : hB ∈ holeRegion := by
  simp only [holeRegion, Set.mem_ofPred_eq, hB]
  norm_num
theorem hC_mem_hole : hC ∈ holeRegion := by
  simp only [holeRegion, Set.mem_ofPred_eq, hC]
  norm_num

theorem seg_AB_sub_hole : segment ℝ hA hB ⊆ holeRegion :=
  convex_holeRegion.segment_subset hA_mem_hole hB_mem_hole
theorem seg_BC_sub_hole : segment ℝ hB hC ⊆ holeRegion :=
  convex_holeRegion.segment_subset hB_mem_hole hC_mem_hole
theorem seg_CA_sub_hole : segment ℝ hC hA ⊆ holeRegion :=
  convex_holeRegion.segment_subset hC_mem_hole hA_mem_hole

/-! Side parameterizations: frontier points on a line lie on its segment. -/

theorem mem_seg_AB_of_L1 (p : plane)
    (heq : p 0 - 3 * p 1 = -1)
    (h2 : 2 * p 0 - p 1 ≤ 4)
    (h3 : 1 ≤ 3 * p 0 - 4 * p 1) : p ∈ segment ℝ hA hB := by
  have hlo : 7 / 5 ≤ p 0 := by linarith
  have hhi : p 0 ≤ 13 / 5 := by linarith
  set t : ℝ := (p 0 - 7 / 5) / (6 / 5) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    apply div_nonneg _ (by norm_num)
    linarith
  have ht1 : t ≤ 1 := by
    rw [ht]
    have h6 : (0:ℝ) < 6 / 5 := by norm_num
    rw [div_le_one h6]
    linarith
  have hmem : (AffineMap.lineMap hA hB) t ∈ segment ℝ hA hB :=
    lineMap_mem_segment ℝ hA hB ⟨ht0, ht1⟩
  have hpeq : p = (AffineMap.lineMap hA hB) t := by
    rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    apply PiLp.ext
    intro i
    fin_cases i
    · simp only [Fin.mk_zero]
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have hb0 : hB 0 = 13 / 5 := by simp [hB]
      have ha0 : hA 0 = 7 / 5 := by simp [hA]
      rw [hb0, ha0, ht]
      field_simp
      ring
    · simp only [Fin.mk_one]
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have hb1 : hB 1 = 6 / 5 := by simp [hB]
      have ha1 : hA 1 = 4 / 5 := by simp [hA]
      rw [hb1, ha1, ht]
      field_simp
      linarith
  rw [hpeq]
  exact hmem

theorem mem_seg_BC_of_L2 (p : plane)
    (h1 : p 0 - 3 * p 1 ≤ -1)
    (heq : 2 * p 0 - p 1 = 4)
    (h3 : 1 ≤ 3 * p 0 - 4 * p 1) : p ∈ segment ℝ hB hC := by
  have hlo : 13 / 5 ≤ p 0 := by linarith
  have hhi : p 0 ≤ 3 := by linarith
  set t : ℝ := (p 0 - 13 / 5) / (2 / 5) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    apply div_nonneg _ (by norm_num)
    linarith
  have ht1 : t ≤ 1 := by
    rw [ht]
    have h6 : (0:ℝ) < 2 / 5 := by norm_num
    rw [div_le_one h6]
    linarith
  have hmem : (AffineMap.lineMap hB hC) t ∈ segment ℝ hB hC :=
    lineMap_mem_segment ℝ hB hC ⟨ht0, ht1⟩
  have hpeq : p = (AffineMap.lineMap hB hC) t := by
    rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    apply PiLp.ext
    intro i
    fin_cases i
    · simp only [Fin.mk_zero]
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have hc0 : hC 0 = 3 := by simp [hC]
      have hb0 : hB 0 = 13 / 5 := by simp [hB]
      rw [hc0, hb0, ht]
      field_simp
      ring
    · simp only [Fin.mk_one]
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have hc1 : hC 1 = 2 := by simp [hC]
      have hb1 : hB 1 = 6 / 5 := by simp [hB]
      rw [hc1, hb1, ht]
      field_simp
      linarith
  rw [hpeq]
  exact hmem

theorem mem_seg_CA_of_L3 (p : plane)
    (h1 : p 0 - 3 * p 1 ≤ -1)
    (h2 : 2 * p 0 - p 1 ≤ 4)
    (heq : 3 * p 0 - 4 * p 1 = 1) : p ∈ segment ℝ hC hA := by
  have hlo : 7 / 5 ≤ p 0 := by linarith
  have hhi : p 0 ≤ 3 := by linarith
  set t : ℝ := (3 - p 0) / (8 / 5) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    apply div_nonneg _ (by norm_num)
    linarith
  have ht1 : t ≤ 1 := by
    rw [ht]
    have h6 : (0:ℝ) < 8 / 5 := by norm_num
    rw [div_le_one h6]
    linarith
  have hmem : (AffineMap.lineMap hC hA) t ∈ segment ℝ hC hA :=
    lineMap_mem_segment ℝ hC hA ⟨ht0, ht1⟩
  have hpeq : p = (AffineMap.lineMap hC hA) t := by
    rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    apply PiLp.ext
    intro i
    fin_cases i
    · simp only [Fin.mk_zero]
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have ha0 : hA 0 = 7 / 5 := by simp [hA]
      have hc0 : hC 0 = 3 := by simp [hC]
      rw [ha0, hc0, ht]
      field_simp
      ring
    · simp only [Fin.mk_one]
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      have ha1 : hA 1 = 4 / 5 := by simp [hA]
      have hc1 : hC 1 = 2 := by simp [hC]
      rw [ha1, hc1, ht]
      field_simp
      linarith
  rw [hpeq]
  exact hmem

/-! Frontier equals the three sides. -/

theorem frontier_holeRegion_eq : frontier holeRegion = holeRegion \ holeInterior := by
  have h : frontier holeRegion = closure holeRegion \ interior holeRegion := rfl
  rw [h, isClosed_holeRegion.closure_eq, interior_holeRegion_eq]

theorem edge_AB_mem : (hA, hB) ∈ cyclicEdges holeVerts := by
  rw [cyclicEdges_holeVerts]
  simp
theorem edge_BC_mem : (hB, hC) ∈ cyclicEdges holeVerts := by
  rw [cyclicEdges_holeVerts]
  simp
theorem edge_CA_mem : (hC, hA) ∈ cyclicEdges holeVerts := by
  rw [cyclicEdges_holeVerts]
  simp

theorem boundary_subset_frontier : boundarySet holeVerts ⊆ frontier holeRegion := by
  intro p hp
  simp only [boundarySet, Set.mem_ofPred_eq] at hp
  obtain ⟨e, he, hmem⟩ := hp
  rw [cyclicEdges_holeVerts] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rw [frontier_holeRegion_eq]
  simp only [Set.mem_sdiff]
  rcases he with rfl | rfl | rfl
  · refine ⟨seg_AB_sub_hole hmem, ?_⟩
    have hline := seg_AB_sub_L1 hmem
    simp only [L1, Set.mem_ofPred_eq] at hline
    intro h
    simp only [holeInterior, Set.mem_ofPred_eq] at h
    obtain ⟨s1, _s2, _s3⟩ := h
    linarith
  · refine ⟨seg_BC_sub_hole hmem, ?_⟩
    have hline := seg_BC_sub_L2 hmem
    simp only [L2, Set.mem_ofPred_eq] at hline
    intro h
    simp only [holeInterior, Set.mem_ofPred_eq] at h
    obtain ⟨_s1, s2, _s3⟩ := h
    linarith
  · refine ⟨seg_CA_sub_hole hmem, ?_⟩
    have hline := seg_CA_sub_L3 hmem
    simp only [L3, Set.mem_ofPred_eq] at hline
    intro h
    simp only [holeInterior, Set.mem_ofPred_eq] at h
    obtain ⟨_s1, _s2, s3⟩ := h
    linarith

theorem frontier_subset_boundary : frontier holeRegion ⊆ boundarySet holeVerts := by
  intro p hp
  rw [frontier_holeRegion_eq] at hp
  simp only [Set.mem_sdiff] at hp
  obtain ⟨hreg, hnout⟩ := hp
  simp only [holeRegion, Set.mem_ofPred_eq] at hreg
  obtain ⟨h1, h2, h3⟩ := hreg
  simp only [boundarySet, Set.mem_ofPred_eq]
  by_cases hs1 : p 0 - 3 * p 1 < -1
  · by_cases hs2 : 2 * p 0 - p 1 < 4
    · by_cases hs3 : (1 : ℝ) < 3 * p 0 - 4 * p 1
      · exfalso
        apply hnout
        simp only [holeInterior, Set.mem_ofPred_eq]
        exact ⟨hs1, hs2, hs3⟩
      · have heq3 : 3 * p 0 - 4 * p 1 = 1 := le_antisymm (not_lt.mp hs3) h3
        exact ⟨(hC, hA), edge_CA_mem, mem_seg_CA_of_L3 p h1 h2 heq3⟩
    · have heq2 : 2 * p 0 - p 1 = 4 := le_antisymm h2 (not_lt.mp hs2)
      exact ⟨(hB, hC), edge_BC_mem, mem_seg_BC_of_L2 p h1 heq2 h3⟩
  · have heq1 : p 0 - 3 * p 1 = -1 := le_antisymm h1 (not_lt.mp hs1)
    exact ⟨(hA, hB), edge_AB_mem, mem_seg_AB_of_L1 p heq1 h2 h3⟩

theorem frontier_holeRegion : frontier holeRegion = boundarySet holeVerts :=
  Set.Subset.antisymm frontier_subset_boundary boundary_subset_frontier

/-! Hole polygon and one-hole workspace. -/

noncomputable def holePoly : Poly where
  vertices := holeVerts
  region := holeRegion
  boundary_eq := frontier_holeRegion
  closed_region := isClosed_holeRegion
  bounded := isBounded_holeRegion
  interior_nonempty := interiorNonempty_holeRegion
  simple := simple_holeVerts

theorem holeRegion_subset_slantInterior : holeRegion ⊆ slantTriInterior := by
  intro p hp
  simp only [holeRegion, Set.mem_ofPred_eq] at hp
  simp only [slantTriInterior, Set.mem_ofPred_eq]
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨by linarith, by linarith, by linarith⟩

theorem hole_inside_proof :
    ∀ h ∈ ([holePoly] : List Poly), closure h.region ⊆ interior slantTriPoly.region := by
  intro h he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  show closure holeRegion ⊆ interior slantTriRegion
  rw [isClosed_holeRegion.closure_eq, frontier_interior_eq]
  exact holeRegion_subset_slantInterior

theorem holes_disjoint_proof :
    List.Pairwise
      (fun h₁ h₂ => Disjoint (closure h₁.region) (closure h₂.region))
      ([holePoly] : List Poly) := by
  simp

noncomputable def oneHoleWorkspace : Workspace where
  outer := slantTriPoly
  holes := [holePoly]
  hole_inside := hole_inside_proof
  holes_disjoint := holes_disjoint_proof

/-!
Tests for the one-hole workspace fixture over the slanted triangle.

Covers free-space membership (hole interior excluded, outer interior point
included) and the vertex count. For polygonal configuration-space obstacles
see LaValle, Planning Algorithms, Sec. 6.2.1.

This file appends after the stub and hole declarations in the test module
namespace `Cslib.Planning.MotionPlanning.PolygonalWorkspace`.
-/

/-- Free-space witness: outer interior, outside the hole (x-3y=-3/2<0, 2x-y=9/2<5 outer-strict; 2x-y=9/2>4 violates hole half-plane 2). -/
noncomputable def holeFreePoint : plane := !₂[(3 : ℝ), (3 / 2 : ℝ)]

/-! Free-space membership tests. -/

theorem holeCenter_mem_holeUnion : holeCenter ∈ holeUnion [holePoly] := by
  rw [holeUnion_cons, holeUnion_nil]
  exact Set.mem_union_left _ (holeInterior_subset holeCenter_mem)

theorem holeCenter_not_free : holeCenter ∉ oneHoleWorkspace.freeSpace := by
  show holeCenter ∉ interior slantTriPoly.region \ holeUnion [holePoly]
  simp only [Set.mem_sdiff]
  intro h
  exact h.2 holeCenter_mem_holeUnion

theorem holeFreePoint_mem_strict : holeFreePoint ∈ slantTriInterior := by
  simp only [holeFreePoint, slantTriInterior, Set.mem_ofPred_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num

theorem holeFreePoint_mem_interior :
    holeFreePoint ∈ interior slantTriPoly.region := by
  show holeFreePoint ∈ interior slantTriRegion
  rw [frontier_interior_eq]
  exact holeFreePoint_mem_strict

theorem holeFreePoint_not_hole : holeFreePoint ∉ holeRegion := by
  simp only [holeRegion, Set.mem_ofPred_eq, holeFreePoint, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num

theorem holeFreePoint_not_union : holeFreePoint ∉ holeUnion [holePoly] := by
  rw [holeUnion_cons, holeUnion_nil, Set.union_empty]
  exact holeFreePoint_not_hole

theorem holeFreePoint_free : holeFreePoint ∈ oneHoleWorkspace.freeSpace := by
  show holeFreePoint ∈ interior slantTriPoly.region \ holeUnion [holePoly]
  simp only [Set.mem_sdiff]
  exact ⟨holeFreePoint_mem_interior, holeFreePoint_not_union⟩

theorem vertexCount_oneHole : oneHoleWorkspace.vertexCount = 6 := by
  simp [Workspace.vertexCount, vertexCountOf, oneHoleWorkspace, slantTriPoly,
    slantTriVerts, holePoly, holeVerts]

#print axioms frontier_holeRegion
#print axioms oneHoleWorkspace

end Cslib.Planning.MotionPlanning.PolygonalWorkspace
