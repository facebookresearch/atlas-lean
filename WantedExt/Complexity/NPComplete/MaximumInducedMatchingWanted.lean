/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM INDUCED MATCHING is NP-complete

Source:
L. J. Stockmeyer and V. V. Vazirani, "NP-completeness of some generalizations of the maximum
matching problem", Information Processing Letters 15 (1982), 14-19; K. Cameron, "Induced
matchings", Discrete Applied Mathematics 24 (1989), 97-102 (NP-completeness for bipartite
graphs, polynomial for chordal graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatching

/-!
# MAXIMUM INDUCED MATCHING is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has an induced matching
of at least `K` edges: a set of pairwise disjoint edges with no edge of the graph joining two
different matched edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A maximum-induced-matching instance: vertex count, edge list, bound. -/
abbrev MaximumInducedMatchingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : MaximumInducedMatchingInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- An induced matching of at least `K` edges. -/
def MaximumInducedMatchingFeasible
    (i : MaximumInducedMatchingInstance) : Prop :=
  ∃ M : List (ℕ × ℕ), M.Sublist i.2.1 ∧ i.2.2 ≤ M.length ∧
    (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
      e1.1 ≠ e2.1 ∧ e1.1 ≠ e2.2 ∧ e1.2 ≠ e2.1 ∧ e1.2 ≠ e2.2) ∧
    ∀ e ∈ i.2.1, ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
      ¬ ((e.1 = e1.1 ∨ e.1 = e1.2) ∧ (e.2 = e2.1 ∨ e.2 = e2.2) ∨
        (e.2 = e1.1 ∨ e.2 = e1.2) ∧ (e.1 = e2.1 ∨ e.1 = e2.2))

open Classical in
/-- MAXIMUM INDUCED MATCHING as a decision problem over bitstrings. -/
noncomputable def maximumInducedMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumInducedMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MaximumInducedMatchingFeasible i)
  | none => false

/-- **MAXIMUM INDUCED MATCHING is NP-complete.** Source: L. J. Stockmeyer and V. V. Vazirani,
"NP-completeness of some generalizations of the maximum matching problem", Information
Processing Letters 15 (1982), 14-19; K. Cameron, "Induced matchings", Discrete Applied
Mathematics 24 (1989), 97-102 (NP-completeness for bipartite graphs, polynomial for
chordal graphs). -/
public theorem_wanted maximumInducedMatching_npComplete :
    maximumInducedMatchingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumInducedMatchingDec

end MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatching
