/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on unit 2-interval graphs is NP-complete

Source:
M. C. Francis, D. Gonçalves and P. Ochem, "The maximum clique problem in multiple interval
graphs", Algorithmica 71 (2015), 812-836, doi:10.1007/s00453-013-9828-6, Section 5 (Theorem 10
of arXiv:1201.0043v2: MAXIMUM CLIQUE is NP-complete for unit 2-interval graphs);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitTwoIntervalGraphRecognitionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueUnitTwoInterval

open MetaMathlibExt.Complexity.NPComplete.UnitTwoIntervalGraphRecognition (IsUnitTwoIntervalGraph)

/-!
# CLIQUE on unit 2-interval graphs is NP-complete

INSTANCE: a unit `2`-interval graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a clique of size `K` or more, i.e., a set `V' ⊆ V` with `|V'| ≥ K`
such that every two vertices in `V'` are joined by an edge?

This is CLIQUE ([GT19]) restricted to the unit `2`-interval graphs (ISGCI `gc_877`): the
intersection graphs of families of unions of two disjoint closed intervals of length `1`, one per
vertex, two distinct vertices being adjacent exactly when their unions intersect
(`UnitTwoIntervalGraphRecognition.IsUnitTwoIntervalGraph`, following Ardévol Martínez, Rizzi,
Sikora and Vialette). Francis, Gonçalves and Ochem (Section 1) call a graph unit `2`-interval
when it has a `2`-interval representation in which all intervals have the same length; the
representation built in their NP-hardness proof (Section 5, Figure 12) uses two disjoint
intervals per vertex, all of length `6n`, which rescale to length `1`. The model is not part of
the input. With `n` in binary, only the non-isolated vertices (at most `2|E|`) need a certified
model, with rational endpoints of polynomial size (the conditions are linear inequalities in the
left endpoints), since isolated vertices can always be given unit `2`-intervals far to the right
of it; a clique of size `K ≥ 2` lies among the non-isolated vertices. The graph is simple and
given by an edge list on `Fin n`. The bound `0 < K ≤ |V|` is the instance class of [GT19].

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev CliqueUnitTwoIntervalInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueUnitTwoIntervalInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `0 < K ≤ n`, and the
graph is a unit `2`-interval graph. -/
def WellFormed (i : CliqueUnitTwoIntervalInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ IsUnitTwoIntervalGraph (Graph i)

/-- The graph has a clique of size `K` or more. -/
def CliqueUnitTwoIntervalFeasible (i : CliqueUnitTwoIntervalInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1))

open Classical in
/-- CLIQUE on unit 2-interval graphs as a decision problem over bitstrings. -/
noncomputable def cliqueUnitTwoIntervalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueUnitTwoIntervalInstance) x with
  | some i => decide (WellFormed i ∧ CliqueUnitTwoIntervalFeasible i)
  | none => false

/-- **CLIQUE on unit 2-interval graphs is NP-complete.** Source: Francis, Gonçalves and Ochem
(2015), Section 5; Garey and Johnson (1979), [GT19]. -/
public theorem_wanted cliqueUnitTwoInterval_npComplete :
    cliqueUnitTwoIntervalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueUnitTwoIntervalDec

end MetaMathlibExt.Complexity.NPComplete.CliqueUnitTwoInterval
