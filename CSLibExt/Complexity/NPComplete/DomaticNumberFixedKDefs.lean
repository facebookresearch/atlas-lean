/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMATIC NUMBER for fixed K ≥ 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT3] DOMATIC NUMBER, p. 190
(comment: "Remains NP-complete for any fixed K ≥ 3"; reference: Garey, Johnson, and Tarjan,
1976b).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DomaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DomaticNumberFixedK

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list; the bound `K` is fixed. -/
abbrev DomaticNumberFixedKInstance := ℕ × List (ℕ × ℕ)

/-- The DOMATIC NUMBER instance `(n, E, K)` of a graph `(n, E)` and the fixed bound `K`. -/
def withBound (K : ℕ) (i : DomaticNumberFixedKInstance) :
    DomaticNumber.DomaticNumberInstance :=
  (i.1, i.2, K)

open Classical in
/-- DOMATIC NUMBER for a fixed bound `K` as a decision problem over bitstrings. -/
noncomputable def domaticNumberFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DomaticNumberFixedKInstance) x with
  | some i => decide (DomaticNumber.WellFormed (withBound K i) ∧
      DomaticNumber.DomaticNumberFeasible (withBound K i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DomaticNumberFixedK
