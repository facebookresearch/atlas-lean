/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COGRAPH EDITING is NP-complete

Source:
Y. Liu, J. Wang, J. Guo and J. Chen, "Complexity and parameterized algorithms for Cograph
Editing", Theoretical Computer Science 461 (2012), 45-54, doi:10.1016/j.tcs.2011.11.040.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CographEditing

/-!
# COGRAPH EDITING is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and a nonnegative integer `K`.
QUESTION: can `G` be made `P₄`-free (a cograph) by adding and deleting at most `K` edges?

The edited graph is a `SimpleGraph` `H` on the same vertices; the edges added or deleted are the
symmetric difference `symmDiff G.edgeSet H.edgeSet`. `H` is `P₄`-free when the path on four
vertices (Mathlib's `SimpleGraph.pathGraph 4`) is not an induced subgraph of `H` (Mathlib's
`SimpleGraph.IsIndContained`, as in `InducedPathWanted`); the `P₄`-free graphs are exactly the
cographs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev CographEditingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CographEditingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CographEditingInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- Adding and deleting at most `K` edges of `G` gives a graph with no induced `P₄`. -/
def CographEditingFeasible (i : CographEditingInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), (symmDiff (Graph i).edgeSet H.edgeSet).ncard ≤ i.2.2 ∧
    ¬ (SimpleGraph.pathGraph 4).IsIndContained H

open Classical in
/-- COGRAPH EDITING as a decision problem over bitstrings. -/
noncomputable def cographEditingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CographEditingInstance) x with
  | some i => decide (WellFormed i ∧ CographEditingFeasible i)
  | none => false

/-- **COGRAPH EDITING is NP-complete.** Source: Liu, Wang, Guo and Chen (2012). -/
public theorem_wanted cographEditing_npComplete :
    cographEditingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cographEditingDec

end MetaMathlibExt.Complexity.NPComplete.CographEditing
