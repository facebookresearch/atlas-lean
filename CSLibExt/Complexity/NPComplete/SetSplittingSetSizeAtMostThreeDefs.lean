/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET SPLITTING with sets of size at most 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 221, problem [SP4] SET SPLITTING
(comment: remains NP-complete even if all `c ∈ C` have `|c| ≤ 3`);
L. Lovász, "Coverings and colorings of hypergraphs", in *Proceedings of the Fourth
Southeastern Conference on Combinatorics, Graph Theory, and Computing*, Utilitas Mathematica
(1973), 3-12.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SetSplittingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetSplittingSetSizeAtMostThree

/-- Well-formedness of an instance: it is a well-formed SET SPLITTING instance (every set is a
duplicate-free list of elements of `S`), and every set has at most three elements. -/
def WellFormed (i : SetSplitting.SetSplittingInstance) : Prop :=
  SetSplitting.WellFormed i ∧ ∀ c ∈ i.2, c.length ≤ 3

open Classical in
/-- SET SPLITTING with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def setSplittingSetSizeAtMostThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetSplitting.SetSplittingInstance) x with
  | some i => decide (WellFormed i ∧ SetSplitting.SetSplittingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SetSplittingSetSizeAtMostThree
