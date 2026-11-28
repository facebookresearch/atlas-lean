/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM TEST SET with tests of size at most 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP6] MINIMUM TEST SET;
K. M. J. De Bontridder, B. V. Halldórsson, M. M. Halldórsson, C. A. J. Hurkens,
J. K. Lenstra, R. Ravi and L. Stougie, "Approximation algorithms for the test cover problem",
Mathematical Programming, Series B 98 (2003), 477-491, doi:10.1007/s10107-003-0414-6,
Section 4 (the test cover problem with at most two items per test, TCP2, is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumTestSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumTestSetSizeTwo

open MetaMathlibExt.Complexity.NPComplete.MinimumTestSet

/-- Well-formedness of an instance: it is a well-formed MINIMUM TEST SET instance, every test is
listed in increasing order and has at most two elements, no test is listed twice, and
`0 < K ≤ |C|`. -/
def WellFormed (i : MinimumTestSetInstance) : Prop :=
  MinimumTestSet.WellFormed i ∧ (∀ c ∈ i.2.1, c.Pairwise (· < ·) ∧ c.length ≤ 2) ∧
    i.2.1.Nodup ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- MINIMUM TEST SET with tests of size at most 2 as a decision problem over bitstrings. -/
noncomputable def minimumTestSetSizeTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumTestSetInstance) x with
  | some i => decide (WellFormed i ∧ MinimumTestSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumTestSetSizeTwo
