/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL BATCHING WITH CHAINS AND UNIT PROCESSING TIMES TO MINIMIZE TOTAL WEIGHTED COMPLETION: definitions
# TIME is NP-complete

Source:
S. Albers and P. Brucker, "The complexity of one-machine batching problems", Discrete Applied
Mathematics 47 (1993), 87-107, doi:10.1016/0166-218X(93)90085-3
(`1|chains; pⱼ = 1; s-batch|∑ wⱼCⱼ`);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Sections 2.7 and 8.1 (the
s-batching model) and the table of NP-hard single machine s-batching problems, which lists
`1|chains; pⱼ = 1; s-batch|∑ wⱼCⱼ` as NP-hard in the strong sense (Albers and Brucker);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (serial batching problems).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.ChainsSerialBatchingCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitSerialBatchingWeightedCompletion

open ChainsSerialBatchingCompletionTime (ChainsSerialBatchingCompletionTimeInstance Job Prec
  completionTime)

/-- An instance: an instance of `1|chains; s-batch|∑ Cᵢ` (the processing times, the pairs
`(i, j)` with `i → j`, the set-up time `s` and the bound `K`) and the weights
`w₀, …, wₙ₋₁`. -/
abbrev ChainsUnitSerialBatchingWeightedCompletionInstance :=
  ChainsSerialBatchingCompletionTimeInstance × List ℕ

/-- The weight `wⱼ` of job `j`. -/
def weight (i : ChainsUnitSerialBatchingWeightedCompletionInstance) (j : Job i.1) : ℕ :=
  i.2.getD j 0

/-- Well-formedness of an instance: it is a well-formed instance of `1|chains; s-batch|∑ Cᵢ`
(listed pairs naming jobs and forming a strict partial order that consists of chains), every
processing time is `1`, and there is one weight per job. -/
def WellFormed (i : ChainsUnitSerialBatchingWeightedCompletionInstance) : Prop :=
  ChainsSerialBatchingCompletionTime.WellFormed i.1 ∧ (∀ p ∈ i.1.1, p = 1) ∧
    i.2.length = i.1.1.length

/-- Some batching compatible with the precedence constraints (`j → j'` implies that `j'` is not
in an earlier batch than `j`) has total weighted completion time at most `K`. -/
def ChainsUnitSerialBatchingWeightedCompletionFeasible
    (i : ChainsUnitSerialBatchingWeightedCompletionInstance) : Prop :=
  ∃ β : Job i.1 → ℕ, (∀ j j', Prec i.1 j j' → β j ≤ β j') ∧
    ∑ j, weight i j * completionTime i.1 β j ≤ i.1.2.2.2

open Classical in
/-- SERIAL BATCHING WITH CHAINS AND UNIT PROCESSING TIMES TO MINIMIZE TOTAL WEIGHTED COMPLETION
TIME as a decision problem over bitstrings. -/
noncomputable def chainsUnitSerialBatchingWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainsUnitSerialBatchingWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ ChainsUnitSerialBatchingWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitSerialBatchingWeightedCompletion
