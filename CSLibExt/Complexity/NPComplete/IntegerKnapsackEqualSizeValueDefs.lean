/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER KNAPSACK with `s(u) = v(u)`: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP10] INTEGER KNAPSACK, comment
(p. 247): "Remains NP-complete if `s(u) = v(u)` for all `u ∈ U`" (reference of the entry:
[Lueker, 1975], G. S. Lueker, "Two NP-complete problems in nonnegative integer programming",
Report 178, Computer Science Laboratory, Princeton University (1975); transformation from
SUBSET SUM).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnboundedKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegerKnapsackEqualSizeValue

open UnboundedKnapsack (UnboundedKnapsackInstance UnboundedKnapsackFeasible)

/-- Well-formedness of an instance: every item `(s(u), v(u))` has `s(u) = v(u)` and
`0 < s(u)`, and `B` and `K` are positive. -/
def WellFormed (i : UnboundedKnapsackInstance) : Prop :=
  (∀ u ∈ i.1, u.1 = u.2 ∧ 0 < u.1) ∧ 0 < i.2.1 ∧ 0 < i.2.2

open Classical in
/-- INTEGER KNAPSACK with `s(u) = v(u)` as a decision problem over bitstrings. -/
noncomputable def integerKnapsackEqualSizeValueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnboundedKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ UnboundedKnapsackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntegerKnapsackEqualSizeValue
