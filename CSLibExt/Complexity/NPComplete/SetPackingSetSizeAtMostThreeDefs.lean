/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET PACKING with sets of size at most 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 221, problem [SP3] SET PACKING
(comment: remains NP-complete even if all `c ∈ C` have `|c| ≤ 3`);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SetPackingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetPackingSetSizeAtMostThree

/-- Well-formedness of an instance: it is a well-formed SET PACKING instance (every set is a
duplicate-free list of elements of the universe), every set has at most three elements, and
`0 < K ≤ |C|`. -/
def WellFormed (i : SetPacking.SetPackingInstance) : Prop :=
  SetPacking.WellFormed i ∧ (∀ c ∈ i.2.1, c.length ≤ 3) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

open Classical in
/-- SET PACKING with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def setPackingSetSizeAtMostThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetPacking.SetPackingInstance) x with
  | some i => decide (WellFormed i ∧ SetPacking.SetPackingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SetPackingSetSizeAtMostThree
