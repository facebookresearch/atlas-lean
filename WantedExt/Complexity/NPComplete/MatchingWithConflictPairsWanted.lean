/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATCHING WITH CONFLICT PAIRS is NP-complete

Source:
A. Darmann, U. Pferschy, J. Schauer and G. J. Woeginger, "Paths, trees and matchings under
disjunctive constraints", Discrete Applied Mathematics 159 (2011), 1726-1735,
doi:10.1016/j.dam.2010.12.016.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatchingWithConflictPairs

/-!
# MATCHING WITH CONFLICT PAIRS is NP-complete

The maximum matching problem under negative disjunctive constraints of Darmann, Pferschy,
Schauer and Woeginger (2011), in decision form. An instance is a graph `G = (V, E)`, a set of
conflict pairs of edges of `G` (a negative disjunctive constraint states that the two edges of
a pair cannot be contained simultaneously in a feasible solution; the pairs are the edges of
the conflict graph on `E`), and an integer `K`. The question is whether `G` has a matching with
at least `K` edges that contains no conflict pair.

Darmann et al. prove that the maximum matching problem is NP-hard already for conflict graphs
in which every connected component is a single edge; the stated problem allows any conflict
graph, so it contains that class. NP membership is immediate (a matching is a polynomial-size
certificate).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, edge list, conflict pairs (each a pair of edges, written as
they appear in the edge list), and the bound `K`. -/
abbrev MatchingWithConflictPairsInstance :=
  ℕ × List (ℕ × ℕ) × List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MatchingWithConflictPairsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: a simple edge list on `Fin n` (no loops, no repeated or
reversed edges), and every conflict pair consists of two distinct listed edges. -/
def WellFormed (i : MatchingWithConflictPairsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    ∀ c ∈ i.2.2.1, c.1 ∈ i.2.1 ∧ c.2 ∈ i.2.1 ∧ c.1 ≠ c.2

/-- There is a matching `M` of `G` with at least `K` edges that contains at most one edge of
every conflict pair. -/
def MatchingWithConflictPairsFeasible (i : MatchingWithConflictPairsInstance) : Prop :=
  ∃ M : (Graph i).Subgraph, M.IsMatching ∧ i.2.2.2 ≤ M.edgeSet.ncard ∧
    ∀ c ∈ i.2.2.1, ¬ (s(c.1.1, c.1.2) ∈ Sym2.map Fin.val '' M.edgeSet ∧
      s(c.2.1, c.2.2) ∈ Sym2.map Fin.val '' M.edgeSet)

open Classical in
/-- MATCHING WITH CONFLICT PAIRS as a decision problem over bitstrings. -/
noncomputable def matchingWithConflictPairsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatchingWithConflictPairsInstance) x with
  | some i => decide (WellFormed i ∧ MatchingWithConflictPairsFeasible i)
  | none => false

/-- **MATCHING WITH CONFLICT PAIRS is NP-complete.** Source: Darmann, Pferschy, Schauer and
Woeginger (2011). -/
public theorem_wanted matchingWithConflictPairs_npComplete :
    matchingWithConflictPairsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L matchingWithConflictPairsDec

end MetaMathlibExt.Complexity.NPComplete.MatchingWithConflictPairs
