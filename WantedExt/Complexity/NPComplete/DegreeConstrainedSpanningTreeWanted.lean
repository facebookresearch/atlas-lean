/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE-CONSTRAINED SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), DEGREE-CONSTRAINED
SPANNING TREE (the `K = 2` slice is Hamiltonian path).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTree

/-!
# DEGREE-CONSTRAINED SPANNING TREE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has a spanning tree
whose maximum degree is at most `K`. A connected edge set with `n - 1` edges is a tree, so
acyclicity need not be stated separately; the degree bound is stated by forbidding `K + 1`
incident edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list, bound. -/
abbrev DegreeConstrainedSpanningTreeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : DegreeConstrainedSpanningTreeInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- A spanning tree of maximum degree at most `K`. -/
def DegreeConstrainedSpanningTreeFeasible
    (i : DegreeConstrainedSpanningTreeInstance) : Prop :=
  ∃ T : List (ℕ × ℕ), T.Sublist i.2.1 ∧ T.Nodup ∧ T.length = i.1 - 1 ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 T).Connected ∧
    ∀ v < i.1, ¬ ∃ D : List (ℕ × ℕ), D.Sublist T ∧ D.length = i.2.2 + 1 ∧
      ∀ e ∈ D, e.1 = v ∨ e.2 = v

open Classical in
/-- DEGREE-CONSTRAINED SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def degreeConstrainedSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DegreeConstrainedSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ DegreeConstrainedSpanningTreeFeasible i)
  | none => false

/-- **DEGREE-CONSTRAINED SPANNING TREE is NP-complete.** Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), DEGREE-CONSTRAINED SPANNING TREE (the `K =
2` slice is Hamiltonian path). -/
public theorem_wanted degreeConstrainedSpanningTree_npComplete :
    degreeConstrainedSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L degreeConstrainedSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTree
