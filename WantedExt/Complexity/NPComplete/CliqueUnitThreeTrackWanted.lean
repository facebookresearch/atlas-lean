/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on unit 3-track interval graphs is NP-complete

Source:
M. C. Francis, D. Gonçalves and P. Ochem, "The maximum clique problem in multiple interval
graphs", Algorithmica 71(4) (2015), 812-836, doi:10.1007/s00453-013-9828-6, Theorem 10
("MAXIMUM CLIQUE is NP-complete for unit 2-interval and unit 3-track graphs"; conference
version in WG 2012, Lecture Notes in Computer Science 7551, 57-68; arXiv:1201.0043);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnitMultiTrackIntervalRecognitionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueUnitThreeTrack

open MetaMathlibExt.Complexity.NPComplete.UnitMultiTrackIntervalRecognition
  (IsUnitMultiTrackIntervalGraph)

/-!
# CLIQUE on unit 3-track interval graphs is NP-complete

INSTANCE: a unit 3-track interval graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a clique of size `K` or more, i.e. a subset `V' ⊆ V` with
`|V'| ≥ K` such that every two vertices of `V'` are joined by an edge of `E`?

This is CLIQUE ([GT19]) restricted to the ISGCI class "unit 3-track" (gc_1081): graphs with an
intersection representation on 3 parallel tracks in which every vertex has exactly one interval
on each track and all intervals have the same length. The class is the repository's
`UnitMultiTrackIntervalRecognition.IsUnitMultiTrackIntervalGraph 3`: each vertex `v` gets the
closed unit interval `[l v j, l v j + 1]` on each track `j : Fin 3`, and two distinct vertices
are adjacent exactly when their intervals on some track intersect. The graph is given by its
vertex count and edge list (`Cslib.Complexity.Karp.edgeGraph`); the clique is a `Finset` whose
coercion is Mathlib's `SimpleGraph.IsClique`.

Membership in NP: a graph is a unit 3-track interval graph exactly when its edge set is the union
of the edge sets of 3 unit interval graphs on its vertex set, so the 3 track graphs are a
certificate (unit interval graphs are recognized in linear time), and isolated vertices are
dropped first (their intervals can go far from all others); for `K ≥ 2` a clique of size `K` lies
among the non-isolated vertices, and for `K = 1` the answer is yes. Hardness is Theorem 10 of
Francis, Gonçalves and Ochem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n` (vertices `0, ..., n - 1`), the edge list, and the bound
`K`. -/
abbrev CliqueUnitThreeTrackInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueUnitThreeTrackInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is a unit
3-track interval graph, and `0 < K ≤ n`. -/
def WellFormed (i : CliqueUnitThreeTrackInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    IsUnitMultiTrackIntervalGraph 3 (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- The graph has a clique of size `K` or more. -/
def CliqueUnitThreeTrackFeasible (i : CliqueUnitThreeTrackInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1))

open Classical in
/-- CLIQUE on unit 3-track interval graphs as a decision problem over bitstrings. -/
noncomputable def cliqueUnitThreeTrackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueUnitThreeTrackInstance) x with
  | some i => decide (WellFormed i ∧ CliqueUnitThreeTrackFeasible i)
  | none => false

/-- **CLIQUE on unit 3-track interval graphs is NP-complete.** Source: Francis, Gonçalves and
Ochem (2015), Theorem 10; Garey and Johnson (1979), [GT19]. -/
public theorem_wanted cliqueUnitThreeTrack_npComplete :
    cliqueUnitThreeTrackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueUnitThreeTrackDec

end MetaMathlibExt.Complexity.NPComplete.CliqueUnitThreeTrack
