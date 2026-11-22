/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.ConfigurationSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Data.Real.Sqrt

@[expose] public section

/-!
# Bounded polygonal workspace model (construction stage 1)

A Lean model of a bounded polygonal workspace for planar motion planning:
one bounded simple outer polygon with finitely many pairwise-disjoint closed
simple-polygon holes strictly inside it. The free space `F` is the outer
interior minus the holes. This is the standard polygonal-world setup described
in LaValle, Planning Algorithms, Section 6.2.1 (polygonal representation).

Stage 1 builds only the model and its elementary facts: the vertex-to-region
coupling, the free space and its openness, the vertex count, general position
(pairwise distinct x-coordinates), and a computed triangle boundary chain. No
decomposition construction and no combinatorial count bound yet.

Comment tags used below:

* `DEFINITIONAL` — computed from other data (vertex lists, regions).
* `HYPOTHESIS` — a genuine geometric property each instance must satisfy.
  These are `Prop` fields of the structures (instance hypotheses), not axioms.
-/

namespace Cslib.Planning.MotionPlanning.PolygonalWorkspace

open Set

-- The plane is the provider's Euclidean plane; coordinates are p 0 (x) and p 1 (y).

/-- DEFINITIONAL: close the loop of a vertex list into directed edges.
`cyclicEdgesAux first vs` links consecutive vertices of `vs` and closes the
last vertex back to `first`. -/
def cyclicEdgesAux (first : plane) : List plane → List (plane × plane)
  | [] => []
  | [v] => [(v, first)]
  | v₁ :: v₂ :: rest => (v₁, v₂) :: cyclicEdgesAux first (v₂ :: rest)

/-- DEFINITIONAL: the cyclic edge list of a polygon: consecutive vertex pairs,
closed from the last vertex back to the first. -/
def cyclicEdges : List plane → List (plane × plane)
  | [] => []
  | v :: rest => cyclicEdgesAux v (v :: rest)

/-- DEFINITIONAL: the boundary chain of a vertex list as a set: the union of
the closed segments over the cyclic edges. -/
def boundarySet (vs : List plane) : Set plane :=
  {p | ∃ e ∈ cyclicEdges vs, p ∈ segment ℝ e.1 e.2}

/-- DEFINITIONAL: cyclic adjacency of edge-occurrence indices: `i` and `j`
are adjacent occurrences in an `n`-edge cycle when one follows the other. -/
def edgeAdjacent (i j n : ℕ) : Prop := (i + 1) % n = j ∨ (j + 1) % n = i

/-- DEFINITIONAL: the `i`-th edge occurrence (0-indexed) of a cyclic vertex
list: the `i`-th entry of its computed cyclic edge list. -/
def edgeOcc (vs : List plane) (i : ℕ) (h : i < (cyclicEdges vs).length) : plane × plane :=
  (cyclicEdges vs)[i]'h

/-- HYPOTHESIS (simplicity) on raw vertex data: occurrence-based simplicity.
The vertices are distinct; no edge occurrence is degenerate; non-adjacent
edge occurrences (by cyclic index) have disjoint closed segments, while
adjacent occurrences meet exactly in their common endpoint. -/
def PolySimple (vs : List plane) : Prop :=
  List.Nodup vs ∧
  (∀ e ∈ cyclicEdges vs, e.1 ≠ e.2) ∧
  ∀ (i j : ℕ) (hi : i < (cyclicEdges vs).length) (hj : j < (cyclicEdges vs).length),
    i ≠ j →
    let e₁ := edgeOcc vs i hi
    let e₂ := edgeOcc vs j hj
    (edgeAdjacent i j (cyclicEdges vs).length →
      ∃ p ∈ (({e₁.1, e₁.2} : Set plane) ∩ ({e₂.1, e₂.2} : Set plane)),
        (segment ℝ e₁.1 e₁.2 ∩ segment ℝ e₂.1 e₂.2 : Set plane) = {p}) ∧
    (¬ edgeAdjacent i j (cyclicEdges vs).length →
      Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ e₂.1 e₂.2))

/-- A simple polygon: a cyclic vertex list coupled to its filled region.
`vertices` and `region` are data; the remaining fields are HYPOTHESES, each a
genuine property of the computed boundary/region pair.

A full concrete instance (proving `boundary_eq` for an explicit filled region)
needs the frontier computation for that region, recorded below as a stage-2
need; stage-1 facts about vertex data are stated for any `Poly`/`Workspace`
with the given vertices. -/
structure Poly where
  /-- DEFINITIONAL DATA: the cyclic vertex list. -/
  vertices : List plane
  /-- DEFINITIONAL EVIDENCE: a polygon has at least three vertices. -/
  len_ge : 3 ≤ vertices.length
  /-- COUPLING DATA: the filled region of the polygon. -/
  region : Set plane
  /-- HYPOTHESIS (coupling): the frontier of the region is exactly the
  boundary chain computed from the vertex list. -/
  boundary_eq : frontier region = boundarySet vertices
  /-- HYPOTHESIS: the region is closed (it includes its boundary). -/
  closed_region : IsClosed region
  /-- HYPOTHESIS: the region is bounded. -/
  bounded : Bornology.IsBounded region
  /-- HYPOTHESIS: the region has nonempty interior. -/
  interior_nonempty : (interior region).Nonempty
  /-- HYPOTHESIS (simplicity): occurrence-based simplicity of the vertex
  list: distinct vertices, no degenerate edges, disjoint non-adjacent edge
  occurrences, adjacent occurrences meeting exactly in their common endpoint. -/
  simple : PolySimple vertices

/-- A bounded polygonal workspace: one outer polygon and finitely many holes.
`outer` and `holes` are data; the remaining fields are HYPOTHESES. -/
structure Workspace where
  /-- DEFINITIONAL DATA: the outer bounding polygon. -/
  outer : Poly
  /-- DEFINITIONAL DATA: the hole polygons. -/
  holes : List Poly
  /-- HYPOTHESIS: every hole closure lies strictly inside the outer interior. -/
  hole_inside : ∀ h : Poly, h ∈ holes → closure h.region ⊆ interior outer.region
  /-- HYPOTHESIS: hole closures are pairwise disjoint. -/
  holes_disjoint : List.Pairwise
    (fun h₁ h₂ : Poly => Disjoint (closure h₁.region) (closure h₂.region)) holes

/-- DEFINITIONAL: the union of the hole regions, by recursion on the list. -/
def holeUnion : List Poly → Set plane
  | [] => ∅
  | h :: t => h.region ∪ holeUnion t

/-- DEFINITIONAL: the free space `F`: the outer interior minus the holes. -/
def Workspace.freeSpace (W : Workspace) : Set plane :=
  interior W.outer.region \ holeUnion W.holes

/-- DEFINITIONAL unfolding: the hole union of no holes is empty. -/
theorem holeUnion_nil : holeUnion [] = ∅ := rfl

/-- DEFINITIONAL unfolding: the hole union of a cons. -/
theorem holeUnion_cons (h : Poly) (t : List Poly) :
    holeUnion (h :: t) = h.region ∪ holeUnion t := rfl

/-- The union of closed hole regions is closed (finite union). Uses only the
`closed_region` HYPOTHESIS of each hole. -/
theorem isClosed_holeUnion (l : List Poly)
    (hc : ∀ h : Poly, h ∈ l → IsClosed h.region) :
    IsClosed (holeUnion l) := by
  induction l with
  | nil => rw [holeUnion_nil]; exact isClosed_empty
  | cons h t ih =>
    rw [holeUnion_cons]
    exact IsClosed.union (hc h (List.mem_cons.mpr (Or.inl rfl)))
      (ih (fun h' hm' => hc h' (List.mem_cons.mpr (Or.inr hm'))))

/-- The free space is open: an open set minus a closed (finite-union) set.
Uses `isOpen_interior`, `IsOpen.sdiff`, `IsClosed.union` and the holes'
`closed_region` HYPOTHESES. -/
theorem Workspace.isOpen_freeSpace (W : Workspace) : IsOpen W.freeSpace := by
  unfold Workspace.freeSpace
  exact IsOpen.sdiff isOpen_interior
    (isClosed_holeUnion W.holes (fun h _ => h.closed_region))

/-- DEFINITIONAL: total vertex count from raw vertex data. -/
def vertexCountOf (outerVs : List plane) (holeVs : List (List plane)) : ℕ :=
  outerVs.length + (holeVs.map List.length).sum

/-- DEFINITIONAL: the workspace vertex count `n`: outer vertices plus all
hole vertices. -/
def Workspace.vertexCount (W : Workspace) : ℕ :=
  vertexCountOf W.outer.vertices (W.holes.map Poly.vertices)

/-- The workspace count unfolds to outer length plus hole lengths. -/
theorem Workspace.vertexCount_eq (W : Workspace) : W.vertexCount =
    W.outer.vertices.length + ((W.holes.map Poly.vertices).map List.length).sum :=
  rfl

/-- DEFINITIONAL: x-coordinates of a vertex list. -/
def xCoordsOf (vs : List plane) : List ℝ := vs.map (fun p => p 0)

/-- DEFINITIONAL: general position on raw vertex data: pairwise distinct
x-coordinates. -/
def generalPositionOf (vs : List plane) : Prop :=
  (xCoordsOf vs).Pairwise (· ≠ ·)

/-- DEFINITIONAL: all workspace vertices, outer then holes concatenated. -/
def Workspace.allVertices (W : Workspace) : List plane :=
  W.outer.vertices ++ (W.holes.map Poly.vertices).flatten

/-- DEFINITIONAL: general position of a workspace. -/
def Workspace.GeneralPosition (W : Workspace) : Prop :=
  generalPositionOf W.allVertices

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
  refine ⟨nodup_slantedVerts, noZero_slantedVerts, ?_⟩
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

/-- With no holes, the workspace count is the outer length. -/
theorem Workspace.vertexCount_of_holes_nil (W : Workspace) (h : W.holes = []) :
    W.vertexCount = W.outer.vertices.length := by
  simp [Workspace.vertexCount, vertexCountOf, h]

/-- With no holes, all vertices are the outer vertices. -/
theorem Workspace.allVertices_of_holes_nil (W : Workspace) (h : W.holes = []) :
    W.allVertices = W.outer.vertices := by
  simp [Workspace.allVertices, h]

/-- Any hole-free workspace with 4 outer vertices has count 4. -/
theorem Workspace.vertexCount_square (W : Workspace)
    (hlen : W.outer.vertices.length = 4) (h : W.holes = []) :
    W.vertexCount = 4 := by
  rw [W.vertexCount_of_holes_nil h, hlen]

/-- Any hole-free workspace on the unit square is not in general position. -/
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

/-- Membership in a boundary chain unfolds to membership in one edge segment. -/
theorem mem_boundarySet_iff (p : plane) (vs : List plane) :
    p ∈ boundarySet vs ↔ ∃ e ∈ cyclicEdges vs, p ∈ segment ℝ e.1 e.2 := Iff.rfl

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
  rintro ⟨hnodup, -, -⟩
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
  refine ⟨nodup_slantTriVerts, noZero_slantTriVerts, ?_⟩
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

/-- The slanted triangle has x-coordinates `[0, 3, 4]`. -/
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

/- Stage-2 need (`frontier_slantTriRegion`): the `boundary_eq` coupling for the
explicit slanted triangle,
`frontier slantTriRegion = boundarySet slantTriVerts`.
Both inclusions need explicit witnesses: every boundary-chain point lies in
`slantTriRegion` but outside its interior (outward normal witnesses per edge),
and every region point outside the interior lies on an edge segment (via
`slantTriInterior_subset_region`). With it, `slantTriVerts` with
`slantTriRegion` assembles into a `Poly` (via `len_ge_slantTriVerts`,
`isClosed_slantTriRegion`, `isBounded_slantTriRegion`,
`interiorNonempty_slantTriRegion`, `simple_slantTriVerts`), and the hole-free
`Workspace` over that `Poly` has vertex count 3 and general position (via
`vertexCountOf_slantTriVerts`, `generalPositionOf_slantTriVerts`). -/

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

end Cslib.Planning.MotionPlanning.PolygonalWorkspace
