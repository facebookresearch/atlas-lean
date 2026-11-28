/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on circle graphs: definitions

Source:
J. M. Keil, "The complexity of domination problems in circle graphs", Discrete Applied
Mathematics 42(1) (1993), 51-63, doi:10.1016/0166-218X(93)90178-Q;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Domination

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph

/-- An instance: the chords (endpoints `a < b`), one per vertex, and the bound `K`. -/
abbrev DominatingSetCircleGraphInstance := List (ℕ × ℕ) × ℕ

/-- The circle graph of a chord model: two distinct chords are adjacent when their endpoints
interleave. -/
def circleGraph (C : List (ℕ × ℕ)) : SimpleGraph (Fin C.length) :=
  SimpleGraph.fromRel fun j k => C[j].1 < C[k].1 ∧ C[k].1 < C[j].2 ∧ C[j].2 < C[k].2

/-- Well-formedness of an instance: every chord has endpoints `a < b`, all endpoints of all
chords are distinct, and `1 ≤ K ≤ |V|`. -/
def WellFormed (i : DominatingSetCircleGraphInstance) : Prop :=
  (∀ c ∈ i.1, c.1 < c.2) ∧ (i.1.flatMap fun c => [c.1, c.2]).Nodup ∧ 1 ≤ i.2 ∧ i.2 ≤ i.1.length

/-- The circle graph has a dominating set of at most `K` vertices. -/
def DominatingSetCircleGraphFeasible (i : DominatingSetCircleGraphInstance) : Prop :=
  ∃ D : Finset (Fin i.1.length), D.card ≤ i.2 ∧ (circleGraph i.1).IsDominating ↑D

open Classical in
/-- DOMINATING SET on circle graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetCircleGraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetCircleGraphInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetCircleGraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph
