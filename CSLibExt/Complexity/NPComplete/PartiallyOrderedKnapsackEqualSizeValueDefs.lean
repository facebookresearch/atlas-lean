/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIALLY ORDERED KNAPSACK with `s(u) = v(u)`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP12] PARTIALLY ORDERED KNAPSACK,
comment (p. 248): "NP-complete in the strong sense, even if `s(u) = v(u)` for all `u ∈ U`"
(reference of the entry: [Garey and Johnson, ——], unpublished; transformation from CLIQUE);
D. S. Johnson and K. A. Niemi, "On knapsacks, partitions, and a new dynamic programming
technique for trees", Mathematics of Operations Research 8 (1983), 1-14,
doi:10.1287/moor.8.1.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PartiallyOrderedKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsackEqualSizeValue

open PartiallyOrderedKnapsack (PartiallyOrderedKnapsackInstance PartiallyOrderedKnapsackFeasible)

/-- Well-formedness of an instance: a well-formed PARTIALLY ORDERED KNAPSACK instance in which
every element has `s(u) = v(u)`. -/
def WellFormed (i : PartiallyOrderedKnapsackInstance) : Prop :=
  PartiallyOrderedKnapsack.WellFormed i ∧ ∀ u ∈ i.1, u.1 = u.2

open Classical in
/-- PARTIALLY ORDERED KNAPSACK with `s(u) = v(u)` as a decision problem over bitstrings. -/
noncomputable def partiallyOrderedKnapsackEqualSizeValueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartiallyOrderedKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ PartiallyOrderedKnapsackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsackEqualSizeValue
