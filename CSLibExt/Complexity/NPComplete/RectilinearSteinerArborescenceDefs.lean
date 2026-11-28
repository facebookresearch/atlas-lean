/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR STEINER ARBORESCENCE: definitions

Source:
W. Shi and C. Su, "The rectilinear Steiner arborescence problem is NP-complete", SIAM Journal on
Computing 35 (2006), 729-740, doi:10.1137/S0097539704371353.
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Quiver.Arborescence
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearSteinerArborescence

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

end MetaMathlibExt.Complexity.NPComplete.RectilinearSteinerArborescence
