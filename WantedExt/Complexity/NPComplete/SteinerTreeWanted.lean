/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), STEINER TREE IN GRAPHS;
R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTree

/-!
# STEINER TREE is NP-complete

An undirected weighted graph, a list of terminals, and a budget `K`. The question is whether
some sublist of edges of total weight at most `K` connects all terminals. Weights are positive,
and there is at most one weighted edge per unordered vertex pair, so the edge list is a
weighted simple graph. A connecting edge set contains a tree of no greater weight, so
acyclicity need not be stated separately.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A Steiner tree instance: vertex count, weighted edges (endpoints, weight), terminals,
budget. -/
abbrev SteinerTreeInstance := ℕ × List (ℕ × ℕ × ℕ) × List ℕ × ℕ


/-- The unweighted graph of a candidate edge set. -/
def Graph (i : SteinerTreeInstance) (T : List (ℕ × ℕ × ℕ)) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (T.map fun e => (e.1, e.2.1))


/-- Well-formedness of an instance. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2) ∧
    (∀ e1 ∈ i.2.1, ∀ e2 ∈ i.2.1,
      (e1.1 = e2.1 ∧ e1.2.1 = e2.2.1 ∨ e1.1 = e2.2.1 ∧ e1.2.1 = e2.1) → e1 = e2) ∧
    i.2.2.1.Nodup ∧ ∀ t ∈ i.2.2.1, t < i.1

/-- Edges of total weight at most `K` connecting all terminals. -/
def SteinerTreeFeasible
    (i : SteinerTreeInstance) : Prop :=
  ∃ T : List (ℕ × ℕ × ℕ), T.Sublist i.2.1 ∧ (T.map (fun e => e.2.2)).sum ≤ i.2.2.2 ∧
    (∀ t ∈ i.2.2.1, t < i.1) ∧
    ∀ a ∈ i.2.2.1, ∀ ha : a < i.1, ∀ b ∈ i.2.2.1, ∀ hb : b < i.1,
      (Graph i T).Reachable ⟨a, ha⟩ ⟨b, hb⟩

open Classical in
/-- STEINER TREE as a decision problem over bitstrings. -/
noncomputable def steinerTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), STEINER TREE IN GRAPHS; R. M. Karp, "Reducibility among
combinatorial problems" (1972). -/
public theorem_wanted steinerTree_npComplete :
    steinerTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTree
