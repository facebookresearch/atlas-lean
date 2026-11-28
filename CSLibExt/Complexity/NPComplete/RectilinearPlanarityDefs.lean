/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR PLANARITY TESTING: definitions

Source:
A. Garg and R. Tamassia, "On the computational complexity of upward and rectilinear planarity
testing", SIAM Journal on Computing 31 (2001), 601-625, doi:10.1137/S0097539794277123.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearPlanarity

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

end MetaMathlibExt.Complexity.NPComplete.RectilinearPlanarity
