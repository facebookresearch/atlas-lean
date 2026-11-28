/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EPT GRAPH RECOGNITION: definitions

Source:
M. C. Golumbic and R. E. Jamison, "Edge and vertex intersection of paths in a tree", Discrete
Mathematics 55 (1985), 151-159, doi:10.1016/0012-365X(85)90043-3;
A. Boyacı, T. Ekim, M. Shalom and S. Zaks, "Graphs of edge-intersecting non-splitting paths in a
tree: representations of holes, Part I", arXiv:1309.2898, Section 1.2 ("it is shown that EPT
graph recognition is NP-complete", citing Golumbic and Jamison, Discrete Mathematics 55);
L. Alcón, M. Gutierrez and M. P. Mazzoleni, "Helly EPT graphs on bounded degree trees:
forbidden induced subgraphs and efficient recognition", arXiv:1604.08775, Section 2 (the
definition of an EPT representation used below).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EptGraphRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev EptGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EptGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : EptGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `(P, T)` is an EPT representation of `G`: `T` is a tree, every `P v` (a walk of `T` from
`a v` to `b v`) is a path, and two distinct vertices `u, v` of `G` are adjacent if and only if
`P u` and `P v` have a common edge. -/
def IsEPTRepresentation {V : Type*} (G : SimpleGraph V) {m : ℕ} (T : SimpleGraph (Fin m))
    (a b : V → Fin m) (P : ∀ v, T.Walk (a v) (b v)) : Prop :=
  T.IsTree ∧ (∀ v, (P v).IsPath) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ ∃ e, e ∈ (P u).edges ∧ e ∈ (P v).edges)

/-- The graph of the instance is EPT: it has an EPT representation on some host tree. -/
def EptGraphRecognitionFeasible (i : EptGraphRecognitionInstance) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (a b : Fin i.1 → Fin m) (P : ∀ v, T.Walk (a v) (b v)),
    IsEPTRepresentation (Graph i) T a b P

open Classical in
/-- EPT GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def eptGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EptGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ EptGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EptGraphRecognition
