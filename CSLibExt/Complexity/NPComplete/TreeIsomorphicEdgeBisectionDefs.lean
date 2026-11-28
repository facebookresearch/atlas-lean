/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ISOMORPHIC EDGE BISECTION OF TREES: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fourth edition), Journal of
Algorithms 3 (1982), 288-300, doi:10.1016/0196-6774(82)90026-8, comment to problem [2]
PARTITIONED GRAPH ISOMORPHISM (attribution: R. L. Graham and R. W. Robinson, private
communication (1982); no published proof was available to us).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreeIsomorphicEdgeBisection

/-- An instance: the vertex count `n` (vertices `0, ..., n - 1`) and the edge list. -/
abbrev TreeIsomorphicEdgeBisectionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TreeIsomorphicEdgeBisectionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and that graph is a
tree. -/
def WellFormed (i : TreeIsomorphicEdgeBisectionInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsTree

/-- The edge set of the tree splits into two disjoint parts `T₁`, `T₂` (spanning subgraphs whose
supremum is the tree) with `T₁ ≃g T₂`. -/
def TreeIsomorphicEdgeBisectionFeasible (i : TreeIsomorphicEdgeBisectionInstance) : Prop :=
  ∃ T₁ T₂ : SimpleGraph (Fin i.1),
    Disjoint T₁ T₂ ∧ T₁ ⊔ T₂ = Graph i ∧ Nonempty (T₁ ≃g T₂)

open Classical in
/-- ISOMORPHIC EDGE BISECTION OF TREES as a decision problem over bitstrings. -/
noncomputable def treeIsomorphicEdgeBisectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreeIsomorphicEdgeBisectionInstance) x with
  | some i => decide (WellFormed i ∧ TreeIsomorphicEdgeBisectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreeIsomorphicEdgeBisection
