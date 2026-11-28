/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLARITY ON TRIANGLE-FREE GRAPHS: definitions

Source:
R. Churchley and J. Huang, "On the polarity and monopolarity of graphs", Journal of Graph Theory
76 (2014), 138-148, doi:10.1002/jgt.21755 (abstract: "we prove that recognizing polarity or
monopolarity remains NP-complete for triangle-free graphs");
ISGCI, *Information System on Graph Classes and their Inclusions*, class "triangle-free"
(gc_371), problem Polarity: NP-complete, with the reference to Churchley and Huang.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.ClusterDeletionDefs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev PolarityTriangleFreeInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PolarityTriangleFreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- `G` is polar: its vertex set splits into a part `A` inducing a complete multipartite graph and
the rest `Aᶜ`, which induces a disjoint union of cliques (a cluster graph). -/
def IsPolar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ A : Set V, (G.induce A).IsCompleteMultipartite ∧ ClusterDeletion.IsClusterGraph (G.induce Aᶜ)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and the graph is
triangle-free. -/
def WellFormed (i : PolarityTriangleFreeInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).CliqueFree 3

/-- The graph is polar. -/
def PolarityTriangleFreeFeasible (i : PolarityTriangleFreeInstance) : Prop :=
  IsPolar (Graph i)

open Classical in
/-- POLARITY ON TRIANGLE-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def polarityTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolarityTriangleFreeInstance) x with
  | some i => decide (WellFormed i ∧ PolarityTriangleFreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree
