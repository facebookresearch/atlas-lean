/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP MEAN FLOW TIME: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS15] FLOW-SHOP SCHEDULING, p. 241
(comment: with a bound `K` on the sum of the completion times in place of the deadline, the
problem is NP-complete in the strong sense even if `m = 2`);
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopMeanFlowTime

/-- Well-formedness of an instance: the parent's (`0 < m`, every job has `m` tasks, `0 < K`)
and `m = 2`. -/
def WellFormed (i : FlowShopScheduling.FlowShopSchedulingInstance) : Prop :=
  FlowShopScheduling.WellFormed i ∧ i.1 = 2

/-- Some schedule `σ p j` (start of job `j`'s task on processor `p`) is one-to-one on each
processor, runs one task at a time on each processor and each job's tasks in processor order,
and the sum over all jobs of the completion times on the last processor is at most `K`. -/
def TwoProcessorFlowShopMeanFlowTimeFeasible
    (i : FlowShopScheduling.FlowShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ,
    (∀ p, Function.Injective (σ p)) ∧
    (∀ p j k, j ≠ k →
      σ p j + FlowShopScheduling.len i p j ≤ σ p k ∨
        σ p k + FlowShopScheduling.len i p k ≤ σ p j) ∧
    (∀ (p : Fin i.1) (hp : p.1 + 1 < i.1) j,
      σ p j + FlowShopScheduling.len i p j ≤ σ ⟨p.1 + 1, hp⟩ j) ∧
    ∀ p : Fin i.1, p.1 + 1 = i.1 → ∑ j, (σ p j + FlowShopScheduling.len i p j) ≤ i.2.2

open Classical in
/-- TWO-PROCESSOR FLOW-SHOP MEAN FLOW TIME as a decision problem over bitstrings. -/
noncomputable def twoProcessorFlowShopMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FlowShopScheduling.FlowShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorFlowShopMeanFlowTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopMeanFlowTime
