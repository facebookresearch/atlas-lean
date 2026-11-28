/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EXPECTED COMPONENT SUM, upper-bound variant with K = 3 and 0/1 entries,: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP18] EXPECTED COMPONENT SUM,
pp. 224-225 (comment: "The variant in which we ask for a partition with K non-empty sets that
yields a sum of B or less is NP-complete even if K is fixed at 3 and all entries are 0's and
1's.").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ExpectedComponentSumZeroOneDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSumUpperBoundThree

open MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSum

/-- Well-formedness of an instance: the well-formedness of EXPECTED COMPONENT SUM with 0/1
entries, and `K = 3`. -/
def WellFormed (i : ExpectedComponentSumInstance) : Prop :=
  ExpectedComponentSumZeroOne.WellFormed i ∧ i.2.2.1 = 3

/-- Some partition of `C` into `K` non-empty disjoint sets has component sum at most `B`. -/
def UpperBoundFeasible (i : ExpectedComponentSumInstance) : Prop :=
  ∃ f : Fin i.2.1.length → Fin i.2.2.1, Function.Surjective f ∧
    componentSum i.1 i.2.1 f ≤ i.2.2.2

open Classical in
/-- The upper-bound variant of EXPECTED COMPONENT SUM with `K = 3` and 0/1 entries as a
decision problem over bitstrings. -/
noncomputable def expectedComponentSumUpperBoundThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ExpectedComponentSumInstance) x with
  | some i => decide (WellFormed i ∧ UpperBoundFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ExpectedComponentSumUpperBoundThree
