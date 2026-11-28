/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED DIAMETER with 0/1 lengths and K = 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER (p. 205),
comment "If C consists entirely of 0's and 1's, then both the diameter and radius versions are
solvable in polynomial time for trees, but are NP-complete for general graphs, even if K is fixed
at 2 (diameter) or 1 (radius)" (credited there to Perl and Zaks, 1978);
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.WeightedDiameterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedDiameterZeroOne

open MetaMathlibExt.Complexity.NPComplete.WeightedDiameter (WeightedDiameterInstance)

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`, `|C| = |E|`,
`0 < K`), every member of `C` is `0` or `1`, and `K = 2`. -/
def WellFormed (i : WeightedDiameterInstance) : Prop :=
  WeightedDiameter.WellFormed i ∧ (∀ c ∈ i.2.2.1, c = 0 ∨ c = 1) ∧ i.2.2.2 = 2

open Classical in
/-- WEIGHTED DIAMETER with 0/1 lengths and `K = 2` as a decision problem over bitstrings. -/
noncomputable def weightedDiameterZeroOneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ WeightedDiameter.WeightedDiameterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedDiameterZeroOne
