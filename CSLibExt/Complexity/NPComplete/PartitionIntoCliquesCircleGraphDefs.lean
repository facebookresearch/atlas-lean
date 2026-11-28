/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO CLIQUES on circle graphs: definitions

Source:
J. M. Keil and L. Stewart, "Approximating the minimum clique cover and other hard problems in
subtree filament graphs", Discrete Applied Mathematics 154(14) (2006), 1983-1995,
doi:10.1016/j.dam.2006.03.003, Theorem 2.1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import CSLibExt.Complexity.NPComplete.DominatingSetCircleGraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesCircleGraph

open MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph (circleGraph)

/-- An instance: the chords, one per vertex, each given by its endpoints `(a, b)`, and the bound
`K`. -/
abbrev PartitionIntoCliquesCircleGraphInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every chord has endpoints `a < b`, all endpoints of all
chords are distinct, and `0 < K ≤ |V|`. -/
def WellFormed (i : PartitionIntoCliquesCircleGraphInstance) : Prop :=
  (∀ c ∈ i.1, c.1 < c.2) ∧ (i.1.flatMap fun c => [c.1, c.2]).Nodup ∧ 0 < i.2 ∧ i.2 ≤ i.1.length

/-- The vertices of the circle graph split into at most `K` cliques: for some `k ≤ K` there is a
block map `c` whose blocks `c⁻¹(j)`, `j : Fin k`, are cliques of the circle graph. -/
def PartitionIntoCliquesCircleGraphFeasible (i : PartitionIntoCliquesCircleGraphInstance) :
    Prop :=
  ∃ k ≤ i.2, ∃ c : Fin i.1.length → Fin k, ∀ j : Fin k, (circleGraph i.1).IsClique {v | c v = j}

open Classical in
/-- PARTITION INTO CLIQUES on circle graphs as a decision problem over bitstrings. -/
noncomputable def partitionIntoCliquesCircleGraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoCliquesCircleGraphInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoCliquesCircleGraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoCliquesCircleGraph
