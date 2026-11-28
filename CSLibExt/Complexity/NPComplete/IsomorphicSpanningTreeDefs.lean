/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ISOMORPHIC SPANNING TREE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND8] ISOMORPHIC SPANNING TREE
(transformation from HAMILTONIAN PATH, the case where `T` is a path);
C. H. Papadimitriou and M. Yannakakis, "The complexity of restricted spanning tree problems",
Journal of the ACM 29(2) (1982), 285-309, doi:10.1145/322307.322309.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTree

/-- An instance: vertex count `n` and edge list of `G`, vertex count `m` and edge list
of `T`. -/
abbrev IsomorphicSpanningTreeInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The graph `G` of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IsomorphicSpanningTreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The tree `T` of the instance as a `SimpleGraph (Fin m)`. -/
def TreeGraph (i : IsomorphicSpanningTreeInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: both edge lists describe simple graphs (no duplicate
edges in either orientation, no self-loops, endpoints in range), and `T` is a tree. -/
def WellFormed (i : IsomorphicSpanningTreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2,
      e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2) ∧
    (TreeGraph i).IsTree

/-- `G` contains a spanning tree isomorphic to `T`: a tree `H` on all vertices of `G`, with
`H ≤ G`, and a graph isomorphism `H ≃g T`. -/
def IsomorphicSpanningTreeFeasible (i : IsomorphicSpanningTreeInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧ H.IsTree ∧ Nonempty (H ≃g TreeGraph i)

open Classical in
/-- ISOMORPHIC SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def isomorphicSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IsomorphicSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ IsomorphicSpanningTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTree
