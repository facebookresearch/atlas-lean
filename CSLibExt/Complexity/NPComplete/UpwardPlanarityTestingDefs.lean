/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UPWARD PLANARITY TESTING: definitions

Source:
A. Garg and R. Tamassia, "On the computational complexity of upward and rectilinear planarity
testing", SIAM Journal on Computing 31 (2001), 601-625, doi:10.1137/S0097539794277123;
G. Di Battista and R. Tamassia, "Algorithms for plane representations of acyclic digraphs",
Theoretical Computer Science 61 (1988), 175-198, doi:10.1016/0304-3975(88)90123-5.
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UpwardPlanarityTesting

/-- An instance: vertex count `n` (vertices `Fin n`) and the arc list; `(u, v)` is an arc from
`u` to `v`. -/
abbrev UpwardPlanarityTestingInstance := ℕ × List (ℕ × ℕ)

/-- The digraph of the instance on `Fin n`: `u → v` is an arc iff `(u, v)` is in the arc
list. -/
def Graph (i : UpwardPlanarityTestingInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2

/-- Well-formedness of an instance: the arc list has no repeated arcs, its endpoints are
vertices, and the digraph is acyclic (no vertex reaches itself by a nonempty directed path). -/
def WellFormed (i : UpwardPlanarityTestingInstance) : Prop :=
  i.2.Nodup ∧ (∀ a ∈ i.2, a.1 < i.1 ∧ a.2 < i.1) ∧
    ∀ v, ¬ Relation.TransGen (Graph i).Adj v v

/-- A planar straight-line upward drawing of a digraph `G`: distinct vertices go to distinct
points, every arc `u → v` goes strictly upward (`f u` has smaller second coordinate than
`f v`), the segments of two arcs with different endpoint sets meet only in common endpoints,
and a vertex lies on the segment of an arc only if it is an endpoint of that arc. -/
def IsUpwardPlanarDrawing {V : Type*} (G : Digraph V) (f : V → ℝ × ℝ) : Prop :=
  Function.Injective f ∧
    (∀ ⦃u v⦄, G.Adj u v → (f u).2 < (f v).2) ∧
    (∀ ⦃u v x y⦄, G.Adj u v → G.Adj x y → ({u, v} : Set V) ≠ {x, y} →
      SimpleGraph.Segment (f u) (f v) ∩ SimpleGraph.Segment (f x) (f y) ⊆
        ({f u, f v} : Set (ℝ × ℝ)) ∩ {f x, f y}) ∧
    ∀ ⦃u v⦄ w, G.Adj u v → f w ∈ SimpleGraph.Segment (f u) (f v) → w = u ∨ w = v

/-- The digraph of the instance has a planar straight-line upward drawing. -/
def UpwardPlanarityTestingFeasible (i : UpwardPlanarityTestingInstance) : Prop :=
  ∃ f : Fin i.1 → ℝ × ℝ, IsUpwardPlanarDrawing (Graph i) f

open Classical in
/-- UPWARD PLANARITY TESTING as a decision problem over bitstrings. -/
noncomputable def upwardPlanarityTestingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UpwardPlanarityTestingInstance) x with
  | some i => decide (WellFormed i ∧ UpwardPlanarityTestingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UpwardPlanarityTesting
