/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR PLANARITY TESTING is NP-complete

Source:
A. Garg and R. Tamassia, "On the computational complexity of upward and rectilinear planarity
testing", SIAM Journal on Computing 31 (2001), 601-625, doi:10.1137/S0097539794277123.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearPlanarity

/-!
# RECTILINEAR PLANARITY TESTING is NP-complete

"An undirected graph is rectilinear planar if it can be drawn in the plane such that every edge
is a horizontal or vertical segment and no two edges cross" (Garg and Tamassia).

INSTANCE: an undirected graph `G = (V, E)`.
QUESTION: is `G` rectilinear planar?

A drawing places each vertex at a point of `ℝ × ℝ`, injectively, and draws each edge as the
closed straight-line segment between its endpoints (MathlibExt's `SimpleGraph.Segment`). It is
rectilinear when every edge is horizontal or vertical (its endpoints share the first or the
second coordinate), and it has no crossing when two different edges meet only at common
endpoints and no vertex lies on an edge except at the edge's own endpoints. The edge-crossing
condition is the one of MathlibExt's straight-line planarity predicate `SimpleGraph.IsPlanar`,
so a rectilinear planar graph is planar. Every rectilinear planar graph
has maximum degree at most `4`: two edges leaving a vertex in the same of the four axis
directions overlap.

The graph is given by its vertex count `n` (vertices `0, …, n - 1`) and an edge list, as a
`SimpleGraph (Fin n)` through `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list. -/
abbrev RectilinearPlanarityInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : RectilinearPlanarityInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: a simple edge list on the vertices `0, …, n - 1`. -/
def WellFormed (i : RectilinearPlanarityInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `f` is a rectilinear planar drawing of `G`: `f` is injective, every edge is a horizontal or
vertical segment, two different edges meet only at common endpoints, and no vertex lies on an
edge other than at its own endpoints. -/
def IsRectilinearDrawing {V : Type*} (G : SimpleGraph V) (f : V → ℝ × ℝ) : Prop :=
  Function.Injective f ∧
    (∀ ⦃v w⦄, G.Adj v w → (f v).1 = (f w).1 ∨ (f v).2 = (f w).2) ∧
    (∀ ⦃v w x y⦄, G.Adj v w → G.Adj x y →
      ({v, w} : Set V) ≠ {x, y} →
      SimpleGraph.Segment (f v) (f w) ∩ SimpleGraph.Segment (f x) (f y) ⊆
        ({f v, f w} : Set (ℝ × ℝ)) ∩ {f x, f y}) ∧
    ∀ ⦃v w⦄ u, G.Adj v w → f u ∈ SimpleGraph.Segment (f v) (f w) → u = v ∨ u = w

/-- The graph has a rectilinear planar drawing. -/
def RectilinearPlanarityFeasible (i : RectilinearPlanarityInstance) : Prop :=
  ∃ f : Fin i.1 → ℝ × ℝ, IsRectilinearDrawing (Graph i) f

open Classical in
/-- RECTILINEAR PLANARITY TESTING as a decision problem over bitstrings. -/
noncomputable def rectilinearPlanarityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectilinearPlanarityInstance) x with
  | some i => decide (WellFormed i ∧ RectilinearPlanarityFeasible i)
  | none => false

/-- **RECTILINEAR PLANARITY TESTING is NP-complete.** Source: Garg and Tamassia (2001). -/
public theorem_wanted rectilinearPlanarity_npComplete :
    rectilinearPlanarityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectilinearPlanarityDec

end MetaMathlibExt.Complexity.NPComplete.RectilinearPlanarity
