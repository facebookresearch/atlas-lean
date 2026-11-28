/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on unit 2-interval graphs: definitions

Source:
M. C. Francis, D. Gonçalves and P. Ochem, "The maximum clique problem in multiple interval
graphs", Algorithmica 71 (2015), 812-836, doi:10.1007/s00453-013-9828-6, Section 5 (Theorem 10
of arXiv:1201.0043v2: MAXIMUM CLIQUE is NP-complete for unit 2-interval graphs);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnitTwoIntervalGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueUnitTwoInterval

open MetaMathlibExt.Complexity.NPComplete.UnitTwoIntervalGraphRecognition (IsUnitTwoIntervalGraph)

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

end MetaMathlibExt.Complexity.NPComplete.CliqueUnitTwoInterval
