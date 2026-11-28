/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSTRAINED TRIANGULATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND45] CONSTRAINED TRIANGULATION;
E. L. Lloyd, "On triangulations of a set of points in the plane", Proc. 18th Annual Symposium
on Foundations of Computer Science (FOCS 1977), 228-240, doi:10.1109/SFCS.1977.21.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Order.Minimal

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedTriangulation

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, and the coordinates of the
vertices in order, each coordinate an integer `p - q` given as the pair `(p, q)`. -/
abbrev ConstrainedTriangulationInstance := ℕ × List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ))

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ConstrainedTriangulationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The integer coordinates `(x_v, y_v)` of vertex `v`. -/
def coord (i : ConstrainedTriangulationInstance) (v : Fin i.1) : ℤ × ℤ :=
  let c := i.2.2.getD v ((0, 0), (0, 0))
  ((c.1.1 : ℤ) - c.1.2, (c.2.1 : ℤ) - c.2.2)

/-- The point of vertex `v` in the real plane. -/
noncomputable def point (i : ConstrainedTriangulationInstance) (v : Fin i.1) : ℝ × ℝ :=
  ((coord i v).1, (coord i v).2)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), there is one
coordinate pair per vertex, and distinct vertices have distinct points. -/
def WellFormed (i : ConstrainedTriangulationInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.length = i.1 ∧ Function.Injective (coord i)

/-- The segments `[point v, point w]` for the edges `{v, w}` of `T` intersect only at their
endpoints: any two distinct ones meet only in common endpoints. -/
def SegmentsMeetAtEndpoints (i : ConstrainedTriangulationInstance)
    (T : SimpleGraph (Fin i.1)) : Prop :=
  ∀ ⦃v w x y⦄, T.Adj v w → T.Adj x y → s(v, w) ≠ s(x, y) →
    SimpleGraph.Segment (point i v) (point i w) ∩ SimpleGraph.Segment (point i x) (point i y) ⊆
      ({point i v, point i w} : Set (ℝ × ℝ)) ∩ {point i x, point i y}

/-- Some `E' ⊆ E` triangulates the point set: its segments form a maximal set of segments with
endpoints in the point set that intersect only at their endpoints. -/
def ConstrainedTriangulationFeasible (i : ConstrainedTriangulationInstance) : Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ Maximal (SegmentsMeetAtEndpoints i) T

open Classical in
/-- CONSTRAINED TRIANGULATION as a decision problem over bitstrings. -/
noncomputable def constrainedTriangulationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConstrainedTriangulationInstance) x with
  | some i => decide (WellFormed i ∧ ConstrainedTriangulationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConstrainedTriangulation
