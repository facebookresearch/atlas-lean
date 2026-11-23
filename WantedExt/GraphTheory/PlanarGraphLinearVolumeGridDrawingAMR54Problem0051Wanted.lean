/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear-volume 3D grid drawings of planar graphs (Open Problems Project, Problem 51)

The Open Problems Project, Problem 51: does every `n`-vertex planar graph have a 3D grid drawing
with `O(n)` volume? (vertices at distinct integer points, straight non-crossing edges, volume of the
bounding box)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Segment
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MathlibExt.GraphTheory.PlanarGraphLinearVolumeGridDrawingAMR54Problem0051Wanted

/-!
Source: E. D. Demaine, J. S. B. Mitchell and J. O'Rourke (eds.), The Open Problems Project, Problem
51, https://topp.openproblem.net/p51. UnsolvedMath record UM-05500051 (`AMR-054-0051`), dataset
ulamai/UnsolvedMath v1.8.0.

Planarity is MathlibExt's `SimpleGraph.IsPlanar`: an injective placement of the vertices in `ℝ²`
such that the straight segments of two distinct edges meet only in common ends; by Fáry's theorem
this is planarity for finite simple graphs. A 3-dimensional grid drawing is as in Dujmović, Morin
and Wood, Layout of graphs with bounded tree-width (one of the two sources, [48], of Lemma 56 of
Dujmović et al.): distinct points of `ℤ³` for the vertices and straight segments for the edges, such
that edges only intersect at common ends and an edge meets no vertex other than its ends (the
problem's pairwise non-crossing segments; Dujmović et al., §9.3, phrase it with open segments of
which no two intersect). The volume is the number of grid points of the smallest axis-aligned grid
box containing the drawing, stated as the existence of an enclosing box with at most `c n` grid
points. Graphs have at least one vertex.
-/

/-- The point of `ℝ³` with the integer coordinates `a`. -/
def toReal (a : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun i => a i

/-- A 3-dimensional grid drawing of `G` (Dujmović-Morin-Wood): distinct points of `ℤ³` for the
vertices and straight segments for the edges, such that no edge segment passes through a vertex
other than its ends and the segments of two distinct edges meet only in common ends. -/
def IsGridDrawing3 {V : Type} (G : SimpleGraph V) (p : V → Fin 3 → ℤ) : Prop :=
  Function.Injective p ∧
    (∀ u v w, G.Adj u v → w ≠ u → w ≠ v →
      toReal (p w) ∉ segment ℝ (toReal (p u)) (toReal (p v))) ∧
    ∀ u v x y, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
      segment ℝ (toReal (p u)) (toReal (p v)) ∩ segment ℝ (toReal (p x)) (toReal (p y)) ⊆
        {toReal (p u), toReal (p v)} ∩ {toReal (p x), toReal (p y)}

/-- The volume of the drawing is at most `N`: some axis-aligned grid box containing all vertex
points has at most `N` grid points. -/
def HasVolumeAtMost {V : Type} (p : V → Fin 3 → ℤ) (N : ℕ) : Prop :=
  ∃ a b : Fin 3 → ℤ, (∀ v i, a i ≤ p v i ∧ p v i ≤ b i) ∧ ∏ i, (b i - a i + 1) ≤ N

/-- Felsner-Liotta-Wismath's question, with a positive answer: there is `c` such that every planar
graph with `n ≥ 1` vertices has a 3-dimensional grid drawing of volume at most `c n`. -/
def planarGraphsHaveLinearVolumeGridDrawings : Prop :=
  ∃ c : ℕ, ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V), G.IsPlanar →
    ∃ p, IsGridDrawing3 G p ∧ HasVolumeAtMost p (c * Fintype.card V)

/--
Resolved true: Dujmović, Joret, Micek, Morin, Ueckerdt and Wood (Theorem 57) prove that every planar
graph with `n` vertices has a 3-dimensional grid drawing with `O(n)` volume. Source: E. D. Demaine,
J. S. B. Mitchell and J. O'Rourke (eds.), The Open Problems Project, Problem 51,
https://topp.openproblem.net/p51; resolution: V. Dujmović, G. Joret, P. Micek, P. Morin, T. Ueckerdt
and D. R. Wood, Planar graphs have bounded queue-number, FOCS 2019 and J. ACM (2020);
arXiv:1904.04791, Theorem 57: every planar graph with n vertices has a 3-dimensional grid drawing
with O(n) volume (§9.3, from bounded queue-number and track layouts), resolving the open problem of
Felsner, Liotta and Wismath, https://arxiv.org/abs/1904.04791.
-/
public theorem_wanted planarGraphsHaveLinearVolumeGridDrawings_holds :
    planarGraphsHaveLinearVolumeGridDrawings

end MathlibExt.GraphTheory.PlanarGraphLinearVolumeGridDrawingAMR54Problem0051Wanted
