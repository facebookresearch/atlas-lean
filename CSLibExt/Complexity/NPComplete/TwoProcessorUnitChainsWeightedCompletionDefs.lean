/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UNIT-TIME CHAINS SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME: definitions

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (the full text was not available to us);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 5.3
(`P2|pᵢ = 1; chains|∑wᵢCᵢ`, NP-hard in the strong sense, Timkovsky).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Defs.Unbundled
public import CSLibExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsWeightedCompletion

open TwoProcessorTreePrecedenceCompletionTime
  (TwoProcessorTreePrecedenceCompletionTimeInstance Prec IsInTree IsOutTree
    TwoProcessorTreePrecedenceCompletionTimeFeasible)

/-- Well-formedness of an instance: `m = 2`, every processing time is `1`, every listed pair
names two jobs, the listed pairs form a strict partial order, and the order is a set of chains
(at most one immediate successor and at most one immediate predecessor per job). Weights and
`K` are arbitrary natural numbers. -/
def WellFormed (i : TwoProcessorTreePrecedenceCompletionTimeInstance) : Prop :=
  i.1 = 2 ∧ (∀ p ∈ i.2.1, p.1 = 1) ∧
    (∀ p ∈ i.2.2.2, p.1 < i.2.1.length ∧ p.2 < i.2.1.length) ∧
    IsStrictOrder (TwoProcessorTreePrecedenceCompletionTime.Task i) (Prec i) ∧
    IsInTree i ∧ IsOutTree i

open Classical in
/-- TWO-PROCESSOR UNIT-TIME CHAINS SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME as a decision
problem over bitstrings. -/
noncomputable def twoProcessorUnitChainsWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTreePrecedenceCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTreePrecedenceCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsWeightedCompletion
