/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on unit 3-track interval graphs: definitions

Source:
M. C. Francis, D. Gonçalves and P. Ochem, "The maximum clique problem in multiple interval
graphs", Algorithmica 71(4) (2015), 812-836, doi:10.1007/s00453-013-9828-6, Theorem 10
("MAXIMUM CLIQUE is NP-complete for unit 2-interval and unit 3-track graphs"; conference
version in WG 2012, Lecture Notes in Computer Science 7551, 57-68; arXiv:1201.0043);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitMultiTrackIntervalRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueUnitThreeTrack

open MetaMathlibExt.Complexity.NPComplete.UnitMultiTrackIntervalRecognition
  (IsUnitMultiTrackIntervalGraph)

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

end MetaMathlibExt.Complexity.NPComplete.CliqueUnitThreeTrack
