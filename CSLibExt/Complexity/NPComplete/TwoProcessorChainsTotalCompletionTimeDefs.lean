/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR CHAINS SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME: definitions

Source:
J. Du, J. Y.-T. Leung and G. H. Young, "Scheduling chain-structured tasks to minimize makespan
and mean flow time", Information and Computation 92 (1991), 219-236,
doi:10.1016/0890-5401(91)90009-Q;
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 5.3 (`P2|chains|∑Cᵢ`,
NP-hard in the strong sense, Du et al.).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorChainsTotalCompletionTime

open TwoProcessorTreePrecedenceCompletionTime
  (TwoProcessorTreePrecedenceCompletionTimeInstance IsInTree IsOutTree
    TwoProcessorTreePrecedenceCompletionTimeFeasible)

/-- Well-formedness of an instance: it is well-formed for the two-processor tree-precedence
problem (`m = 2`, positive lengths and equal positive weights, `0 < K`, the listed pairs name
tasks and form a strict partial order), the order is a set of chains (at most one immediate
successor and at most one immediate predecessor per task), and every weight is `1`. -/
def WellFormed (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  TwoProcessorTreePrecedenceCompletionTime.WellFormed i ∧ IsInTree i ∧ IsOutTree i ∧
    ∀ p ∈ i.2.1, p.2 = 1

open Classical in
/-- TWO-PROCESSOR CHAINS SCHEDULING TO MINIMIZE TOTAL COMPLETION TIME as a decision problem
over bitstrings. -/
noncomputable def twoProcessorChainsTotalCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTreePrecedenceCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTreePrecedenceCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorChainsTotalCompletionTime
