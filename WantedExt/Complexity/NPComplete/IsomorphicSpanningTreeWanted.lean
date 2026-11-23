/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ISOMORPHIC SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND8] ISOMORPHIC SPANNING TREE
(transformation from HAMILTONIAN PATH, the case where `T` is a path);
C. H. Papadimitriou and M. Yannakakis, "The complexity of restricted spanning tree problems",
Journal of the ACM 29(2) (1982), 285-309, doi:10.1145/322307.322309.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTree

/-!
# ISOMORPHIC SPANNING TREE is NP-complete

An instance is a graph `G = (V, E)` and a tree `T = (V_T, E_T)`. The question is whether `G`
contains a spanning tree isomorphic to `T`, i.e. a subgraph of `G` on all of `V` that is a tree
and is isomorphic to `T`. When `T` is a path this is HAMILTONIAN PATH; Papadimitriou and
Yannakakis (1982) show that it stays NP-complete for other tree families, e.g. full binary
trees.

Both graphs are simple and given by edge lists: `G` on `Fin n`, `T` on `Fin m`. Nothing forces
`m = n`; when they differ no spanning tree of `G` is isomorphic to `T`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **ISOMORPHIC SPANNING TREE is NP-complete.** Source: Garey and Johnson (1979), [ND8];
Papadimitriou and Yannakakis (1982). -/
public theorem_wanted isomorphicSpanningTree_npComplete :
    isomorphicSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L isomorphicSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.IsomorphicSpanningTree
