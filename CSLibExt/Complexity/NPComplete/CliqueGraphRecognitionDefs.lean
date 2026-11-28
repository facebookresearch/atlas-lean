/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE GRAPH (clique graph recognition): definitions

Source:
L. Alcón, L. Faria, C. M. H. de Figueiredo and M. Gutierrez, "The complexity of clique graph
recognition", Theoretical Computer Science 410(21-23) (2009), 2072-2083,
doi:10.1016/j.tcs.2009.01.018.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueGraphRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev CliqueGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- The clique graph `K(H)`: the intersection graph of the maximal cliques of `H`. Its
vertices are the maximal cliques of `H`; two distinct maximal cliques are adjacent when they
share a vertex. -/
def cliqueGraph {V : Type*} (H : SimpleGraph V) :
    SimpleGraph {s : Set V // Maximal H.IsClique s} :=
  SimpleGraph.fromRel fun s t => ((s : Set V) ∩ t).Nonempty

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate
edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CliqueGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `G` is a clique graph: `G` is isomorphic to `K(H)` for some finite simple graph `H`. -/
def CliqueGraphRecognitionFeasible (i : CliqueGraphRecognitionInstance) : Prop :=
  ∃ m : ℕ, ∃ H : SimpleGraph (Fin m), Nonempty (Graph i ≃g cliqueGraph H)

open Classical in
/-- CLIQUE GRAPH as a decision problem over bitstrings. -/
noncomputable def cliqueGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ CliqueGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueGraphRecognition
