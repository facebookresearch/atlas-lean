/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH ORDERABLE GRAPH RECOGNITION: definitions

Source:
D. G. Corneil, E. Köhler, S. Olariu and L. Stewart, "Linear orderings of subfamilies of
AT-free graphs", SIAM Journal on Discrete Mathematics 20 (2006), 105-118,
doi:10.1137/S0895480104445307;
ISGCI (https://www.graphclasses.org/classes/gc_933.html), problem "Recognition" on path
orderable graphs: NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Logic.Equiv.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathOrderableGraphRecognition

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev PathOrderableGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PathOrderableGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : PathOrderableGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `pos` (vertex ↦ position) is a path ordering of `G`: for every triple `u, w, x` in this
order with `u` and `x` non-adjacent, `w` is adjacent to a vertex of every `u, x`-path. -/
def IsPathOrdering {n : ℕ} (G : SimpleGraph (Fin n)) (pos : Fin n ≃ Fin n) : Prop :=
  ∀ u w x, pos u < pos w → pos w < pos x → ¬ G.Adj u x →
    ∀ p : G.Walk u x, p.IsPath → ∃ y ∈ p.support, G.Adj w y

/-- The graph of the instance is path orderable: it has a path ordering. -/
def PathOrderableGraphRecognitionFeasible (i : PathOrderableGraphRecognitionInstance) : Prop :=
  ∃ pos : Fin i.1 ≃ Fin i.1, IsPathOrdering (Graph i) pos

open Classical in
/-- PATH ORDERABLE GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def pathOrderableGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathOrderableGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ PathOrderableGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathOrderableGraphRecognition
