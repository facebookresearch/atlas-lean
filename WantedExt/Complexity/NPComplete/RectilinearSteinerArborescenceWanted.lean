/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR STEINER ARBORESCENCE is NP-complete

Source:
W. Shi and C. Su, "The rectilinear Steiner arborescence problem is NP-complete", SIAM Journal on
Computing 35 (2006), 729-740, doi:10.1137/S0097539704371353.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Quiver.Arborescence
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearSteinerArborescence

/-!
# RECTILINEAR STEINER ARBORESCENCE is NP-complete

INSTANCE: a set of points `P = {p₁, p₂, …, pₙ}` in the first quadrant of the plane, and a
positive integer `k`. QUESTION: is there a rectilinear Steiner arborescence (RSA) for `P` of total
edge length `k` or less? An RSA for `P` is a directed Steiner tree `T` rooted at the origin,
containing all points in `P`, and composed solely of horizontal and vertical line segments
oriented from left to right, or from bottom to top (Shi and Su, Section 1 and the decision
version in Section 2.1).

The points have integer coordinates `(x, y)` with `x, y ≥ 0`. Shi and Su prove NP-completeness
in the strong sense: their reduction produces points whose coordinates are integers "of
polynomial size" (proof of Theorem 2.8), and membership in NP follows from the Hanan property of
Rao, Sadayappan, Hwang and Shor (an optimal RSA uses only the grid lines through the points).

The tree is given by its list `T` of directed edges `(a, b)` from `a` to `b`, with endpoints
anywhere in `ℝ × ℝ` (Steiner points are arbitrary). Its vertices are the origin and the endpoints
of the edges (`vertices`), and `edgeQuiver T` is the quiver on them with an arrow `a ⟶ b` exactly
when `(a, b)` is an edge. `IsRSA P T` says:
* every edge is a horizontal segment oriented from left to right or a vertical segment oriented
  from bottom to top (`IsRectilinearEdge`), and no edge is listed twice;
* distinct edges, as closed segments of the plane, meet only in points that are endpoints of
  both (`NonCrossing`), so the union of the segments is drawn without crossings, overlaps, or a
  vertex inside another edge;
* the quiver is a directed rooted tree rooted at the origin, in Mathlib's sense
  (`Quiver.Arborescence`: a unique path from the root to every vertex);
* every point of `P` is a vertex.
So `T` is a directed Steiner tree rooted at the origin, containing `P`, drawn in the plane with
horizontal and vertical segments oriented to the right or upward; its vertices include every
branch point and every point of `P` (a drawn tree is subdivided there, which changes neither the
drawing nor the length). Each root-to-point path is monotone, hence a shortest rectilinear path.
The total edge length is the sum over the edges of `(b.x - a.x) + (b.y - a.y)`, the length of
the segment.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points `p₁, …, pₙ` of `P`, each a pair `(x, y)` of nonnegative integer
coordinates, and the bound `k`. -/
abbrev RectilinearSteinerArborescenceInstance := List (ℕ × ℕ) × ℕ

/-- The edge `(a, b)` from `a` to `b` is a horizontal segment oriented from left to right or a
vertical segment oriented from bottom to top. -/
def IsRectilinearEdge (e : (ℝ × ℝ) × (ℝ × ℝ)) : Prop :=
  (e.1.2 = e.2.2 ∧ e.1.1 < e.2.1) ∨ (e.1.1 = e.2.1 ∧ e.1.2 < e.2.2)

/-- The length `(b.x - a.x) + (b.y - a.y)` of an edge `(a, b)`; for a horizontal or vertical
segment oriented to the right or upward it is the Euclidean length of the segment. -/
def edgeLength (e : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  (e.2.1 - e.1.1) + (e.2.2 - e.1.2)

/-- The vertices of the edge list `T`: the origin and the endpoints of the edges. -/
def vertices (T : List ((ℝ × ℝ) × (ℝ × ℝ))) : Set (ℝ × ℝ) :=
  {z | z = (0, 0) ∨ ∃ e ∈ T, z = e.1 ∨ z = e.2}

/-- The quiver of `T` on its vertices: an arrow `a ⟶ b` exactly when `(a, b)` is an edge. -/
@[instance_reducible]
def edgeQuiver (T : List ((ℝ × ℝ) × (ℝ × ℝ))) : Quiver (vertices T) where
  Hom a b := PLift (((a : ℝ × ℝ), (b : ℝ × ℝ)) ∈ T)

/-- The origin as a vertex of `T`. -/
def origin (T : List ((ℝ × ℝ) × (ℝ × ℝ))) : vertices T :=
  ⟨(0, 0), Or.inl rfl⟩

/-- Distinct edges of `T`, as closed segments of the plane, meet only in points that are
endpoints of both. -/
def NonCrossing (T : List ((ℝ × ℝ) × (ℝ × ℝ))) : Prop :=
  ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' →
    segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆ ({e.1, e.2} : Set (ℝ × ℝ)) ∩ {e'.1, e'.2}

/-- The edge list `T` is a rectilinear Steiner arborescence for the points `P`: rectilinear
edges oriented right or up, listed once each and drawn without crossings, forming a directed
tree rooted at the origin (`Quiver.Arborescence` of `edgeQuiver T` with root the origin) whose
vertices include every point of `P`. -/
def IsRSA (P : List (ℕ × ℕ)) (T : List ((ℝ × ℝ) × (ℝ × ℝ))) : Prop :=
  (∀ e ∈ T, IsRectilinearEdge e) ∧ T.Nodup ∧ NonCrossing T ∧
    (∃ A : @Quiver.Arborescence (vertices T) (edgeQuiver T), A.root = origin T) ∧
    ∀ p ∈ P, ((p.1 : ℝ), (p.2 : ℝ)) ∈ vertices T

/-- Well-formedness of an instance: `k` is positive. -/
def WellFormed (i : RectilinearSteinerArborescenceInstance) : Prop :=
  0 < i.2

/-- Some rectilinear Steiner arborescence for `P` has total edge length at most `k`. -/
def RectilinearSteinerArborescenceFeasible (i : RectilinearSteinerArborescenceInstance) :
    Prop :=
  ∃ T, IsRSA i.1 T ∧ (T.map edgeLength).sum ≤ i.2

open Classical in
/-- RECTILINEAR STEINER ARBORESCENCE as a decision problem over bitstrings. -/
noncomputable def rectilinearSteinerArborescenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectilinearSteinerArborescenceInstance) x with
  | some i => decide (WellFormed i ∧ RectilinearSteinerArborescenceFeasible i)
  | none => false

/-- **RECTILINEAR STEINER ARBORESCENCE is NP-complete.** Source: Shi and Su (2006). -/
public theorem_wanted rectilinearSteinerArborescence_npComplete :
    rectilinearSteinerArborescenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectilinearSteinerArborescenceDec

end MetaMathlibExt.Complexity.NPComplete.RectilinearSteinerArborescence
