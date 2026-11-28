/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE CONSTRAINED SPANNING TREE for fixed K ≥ 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND1] DEGREE CONSTRAINED SPANNING
TREE, p. 206 (comment: "Remains NP-complete for any fixed K ≥ 2").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DegreeConstrainedSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTreeFixedK

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list; the bound `K` is fixed. -/
abbrev DegreeConstrainedSpanningTreeFixedKInstance := ℕ × List (ℕ × ℕ)

/-- The [ND1] instance `(n, E, K)` of a graph `(n, E)` and the fixed bound `K`. -/
def withBound (K : ℕ) (i : DegreeConstrainedSpanningTreeFixedKInstance) :
    DegreeConstrainedSpanningTree.DegreeConstrainedSpanningTreeInstance :=
  (i.1, i.2, K)

/-- Well-formedness of an instance for the fixed bound `K`: the [ND1] well-formedness of
`(n, E, K)` (`0 < n`, simple edge list) and Garey and Johnson's `K ≤ |V|`. -/
def WellFormed (K : ℕ) (i : DegreeConstrainedSpanningTreeFixedKInstance) : Prop :=
  DegreeConstrainedSpanningTree.WellFormed (withBound K i) ∧ K ≤ i.1

open Classical in
/-- DEGREE CONSTRAINED SPANNING TREE for a fixed bound `K` as a decision problem over
bitstrings. -/
noncomputable def degreeConstrainedSpanningTreeFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DegreeConstrainedSpanningTreeFixedKInstance) x with
  | some i => decide (WellFormed K i ∧
      DegreeConstrainedSpanningTree.DegreeConstrainedSpanningTreeFeasible (withBound K i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTreeFixedK
