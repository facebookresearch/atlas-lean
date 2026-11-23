/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.ConfigurationSpace
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed

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
  3 ≤ vs.length ∧
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

/-- Fewer than three vertices is never simple. -/
theorem not_polySimple_length_lt_three (vs : List plane) (h : vs.length < 3) : ¬ PolySimple vs := fun hs => (Nat.not_le_of_gt h) hs.1
/-- The empty vertex list is not simple. -/
theorem not_polySimple_nil : ¬ PolySimple [] := not_polySimple_length_lt_three [] (by decide)

/-- A simple polygon: a cyclic vertex list coupled to its filled region.
`vertices` and `region` are data; the remaining fields are HYPOTHESES, each a
genuine property of the computed boundary/region pair.

A full concrete instance (proving `boundary_eq` for an explicit filled region)
discharges `boundary_eq` by a frontier computation for its region, with an
example in the test suite; stage-1 facts about vertex data are stated for any
`Poly`/`Workspace` with the given vertices. -/
structure Poly where
  /-- DEFINITIONAL DATA: the cyclic vertex list. -/
  vertices : List plane
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
theorem Poly.len_ge_three (P : Poly) : 3 ≤ P.vertices.length := P.simple.1
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
/-- Membership in a boundary chain unfolds to membership in one edge segment. -/
theorem mem_boundarySet_iff (p : plane) (vs : List plane) :
    p ∈ boundarySet vs ↔ ∃ e ∈ cyclicEdges vs, p ∈ segment ℝ e.1 e.2 := Iff.rfl

end Cslib.Planning.MotionPlanning.PolygonalWorkspace
