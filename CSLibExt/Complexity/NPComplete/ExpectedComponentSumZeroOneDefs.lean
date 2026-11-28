/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED COMPONENT SUM with 0/1 entries: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP18] EXPECTED COMPONENT SUM,
pp. 224-225 (comment: "NP-complete even if all entries are 0's and 1's.").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ExpectedComponentSumDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSumZeroOne

open MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSum

/-- Well-formedness of an instance: the [SP18] well-formedness, and every vector entry is `0`
or `1`. -/
def WellFormed (i : ExpectedComponentSumInstance) : Prop :=
  ExpectedComponentSum.WellFormed i ∧ ∀ v ∈ i.2.1, ∀ x ∈ v, x ≤ 1

open Classical in
/-- EXPECTED COMPONENT SUM with 0/1 entries as a decision problem over bitstrings. -/
noncomputable def expectedComponentSumZeroOneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExpectedComponentSumInstance) x with
  | some i => decide (WellFormed i ∧ ExpectedComponentSumFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSumZeroOne
