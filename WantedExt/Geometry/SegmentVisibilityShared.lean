/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Segment endpoint visibility graphs and simple polygons: shared definitions

Shared helper for the UnsolvedMath entries on Ghosh and Goswami's Conjectures 14, 15 and 16
(Mirzaian's conjectures on Hamiltonian cycles in segment visibility graphs):
`WantedExt/Geometry/SegmentVisibilityHamiltonianCycleAMR131Problem0012Wanted.lean`,
`WantedExt/Geometry/SegmentVisibilityHamiltonianPolygonAMR131Problem0013Wanted.lean` and
`WantedExt/Geometry/CircumscribingPolygonAMR131Problem0014Wanted.lean`.
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace MathlibExt.Geometry.SegmentVisibilityShared

/-!
S. K. Ghosh and P. P. Goswami, *Unsolved problems in visibility graphs of points, segments and
polygons* (arXiv:1012.5187), Section 2: for a set `S` of disjoint line segments with endpoints
`p₁, …, p_{2n}` (`p_{2i-1}`, `p_{2i}` the endpoints of `sᵢ`), two endpoints are mutually visible if
the segment joining them does not intersect any segment of `S` (it may not pass through another
endpoint or graze along a segment), and the segment visibility graph joins mutually visible
endpoints and the two endpoints of every segment. Here the `m` segments are given by an endpoint
family `e : Fin (2 * m) → ℝ × ℝ`, segment `k` joining `e (2k)` and `e (2k + 1)`.

A simple polygon has vertices `v₀, …, v_{n-1}` (`n ≥ 3`) whose edges `[vᵢ, vᵢ₊₁]` (indices mod `n`)
are nondegenerate and meet only at the common vertex of consecutive edges; its region is a compact
set with nonempty interior whose frontier is the polygon (by the Jordan curve theorem this is the
closed region bounded by it, and quantifying over it avoids that theorem).

`seg` and `SegAdj` repeat, under the same names and with the same bodies, the definitions in
`OpenConjectures.ComputerScience.AMR131Problem15`, and `edge`, `IsSimplePolygon` and `IsRegion`
those in `OpenConjectures.Geometry.AMR131Problem36` (round-1 entries for the same problem list):
`WantedExt` cannot import `OpenConjectures`.
-/

/-- Segment `k` of the endpoint family `e`: `[e_{2k}, e_{2k+1}]`. -/
def seg {m : ℕ} (e : Fin (2 * m) → ℝ × ℝ) (k : Fin m) : Set (ℝ × ℝ) :=
  segment ℝ (e ⟨2 * k.val, by omega⟩) (e ⟨2 * k.val + 1, by omega⟩)

/-- Endpoints `i` and `j` are adjacent in the segment visibility graph. -/
def SegAdj {m : ℕ} (e : Fin (2 * m) → ℝ × ℝ) (i j : Fin (2 * m)) : Prop :=
  i ≠ j ∧ (i.val / 2 = j.val / 2 ∨ ∀ k, Disjoint (openSegment ℝ (e i) (e j)) (seg e k))

/-- The endpoint family `e` describes `m` pairwise disjoint nondegenerate closed segments. -/
def IsDisjointSegmentFamily {m : ℕ} (e : Fin (2 * m) → ℝ × ℝ) : Prop :=
  (∀ k : Fin m, e ⟨2 * k.val, by omega⟩ ≠ e ⟨2 * k.val + 1, by omega⟩) ∧
    ∀ k l, k ≠ l → Disjoint (seg e k) (seg e l)

/-- The edge `[vᵢ, vᵢ₊₁]` of a polygon (indices mod `n`). -/
def edge {n : ℕ} (v : Fin n → ℝ × ℝ) (i : Fin n) : Set (ℝ × ℝ) :=
  segment ℝ (v i) (v (finRotate n i))

/-- `v` is a simple polygon: at least three vertices, nondegenerate edges, and edges meeting only at
the common vertex of consecutive edges. -/
def IsSimplePolygon {n : ℕ} (v : Fin n → ℝ × ℝ) : Prop :=
  3 ≤ n ∧ (∀ i, v i ≠ v (finRotate n i)) ∧
    ∀ i j, i ≠ j →
      (j = finRotate n i → edge v i ∩ edge v j = {v j}) ∧
      (i = finRotate n j → edge v i ∩ edge v j = {v i}) ∧
      (j ≠ finRotate n i → i ≠ finRotate n j → Disjoint (edge v i) (edge v j))

/-- `K` is the closed region of the polygon `v`: compact, with nonempty interior, and with the
polygon as frontier. -/
def IsRegion {n : ℕ} (v : Fin n → ℝ × ℝ) (K : Set (ℝ × ℝ)) : Prop :=
  IsCompact K ∧ (interior K).Nonempty ∧ frontier K = ⋃ i, edge v i

end MathlibExt.Geometry.SegmentVisibilityShared
