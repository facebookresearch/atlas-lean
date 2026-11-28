/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT FLOW-SHOP MEAN FLOW TIME: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (comment: with a bound `K` on the sum of the completion times in place of the deadline,
the problem is NP-complete in the strong sense for `m` arbitrary);
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine
scheduling problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.NoWaitFlowShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopMeanFlowTime

/-- There is a no-wait flow-shop schedule (each job's task on processor `p + 1` starts exactly
when its task on processor `p` finishes) whose sum over all jobs of the completion times on
the last processor is at most `K`. -/
def NoWaitFlowShopMeanFlowTimeFeasible
    (i : NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, NoWaitFlowShopScheduling.IsFlowShopSchedule i σ ∧
    (∀ j p q, q.1 = p.1 + 1 → σ q j = σ p j + NoWaitFlowShopScheduling.taskLength i p j) ∧
    ∀ p : Fin i.1, p.1 + 1 = i.1 →
      ∑ j, (σ p j + NoWaitFlowShopScheduling.taskLength i p j) ≤ i.2.2

open Classical in
/-- NO-WAIT FLOW-SHOP MEAN FLOW TIME as a decision problem over bitstrings. -/
noncomputable def noWaitFlowShopMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NoWaitFlowShopScheduling.NoWaitFlowShopSchedulingInstance) x with
  | some i => decide (NoWaitFlowShopScheduling.WellFormed i ∧
      NoWaitFlowShopMeanFlowTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopMeanFlowTime
