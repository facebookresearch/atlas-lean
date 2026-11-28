/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT FLOW-SHOP SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT
FLOW-SHOP SCHEDULING (with the definitions of [SS1], [SS14] and [SS15]);
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine
scheduling problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X;
C. H. Papadimitriou and P. C. Kanellakis, "Flowshop scheduling with limited
temporary storage", Journal of the ACM 27 (1980), 533-549,
doi:10.1145/322203.322213 (already for `m = 4` processors).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling

/-- An instance: the number `m` of processors, the jobs (job `j` is the list
`[l(t₁[j]), …, l(tₘ[j])]` of its task lengths), and the overall deadline `D`. -/
abbrev NoWaitFlowShopSchedulingInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: `m ∈ ℤ⁺`, every job consists of exactly `m` tasks, and
`D ∈ ℤ⁺`. -/
def WellFormed (i : NoWaitFlowShopSchedulingInstance) : Prop :=
  0 < i.1 ∧ (∀ job ∈ i.2.1, job.length = i.1) ∧ 0 < i.2.2

/-- The length `l(t_p[j])` of the task of job `j` executed by processor `p`. -/
def taskLength (i : NoWaitFlowShopSchedulingInstance) (p : Fin i.1) (j : Fin i.2.1.length) :
    ℕ :=
  (i.2.1.get j).getD p 0

/-- `σ` is an open-shop schedule meeting the deadline [SS14]: each `σ p` is a one-processor
schedule [SS1] (one-to-one, and `σ p j > σ p k` implies `σ p j ≥ σ p k + l(t_p[k])`), the
tasks of each job occupy pairwise disjoint intervals, and every task finishes by `D`. -/
def IsOpenShopSchedule (i : NoWaitFlowShopSchedulingInstance)
    (σ : Fin i.1 → Fin i.2.1.length → ℕ) : Prop :=
  (∀ p, Function.Injective (σ p)) ∧
    (∀ p j k, σ p k < σ p j → σ p k + taskLength i p k ≤ σ p j) ∧
    (∀ j p q, p ≠ q →
      Disjoint (Set.Ico (σ p j) (σ p j + taskLength i p j))
        (Set.Ico (σ q j) (σ q j + taskLength i q j))) ∧
    ∀ p j, σ p j + taskLength i p j ≤ i.2.2

/-- `σ` is a flow-shop schedule meeting the deadline [SS15]: an open-shop schedule in which
each job's task on processor `p + 1` starts no earlier than its task on processor `p`
finishes. -/
def IsFlowShopSchedule (i : NoWaitFlowShopSchedulingInstance)
    (σ : Fin i.1 → Fin i.2.1.length → ℕ) : Prop :=
  IsOpenShopSchedule i σ ∧
    ∀ j p q, q.1 = p.1 + 1 → σ p j + taskLength i p j ≤ σ q j

/-- There is a flow-shop schedule meeting the deadline with no waiting: each job's task on
processor `p + 1` starts exactly when its task on processor `p` finishes. -/
def NoWaitFlowShopSchedulingFeasible (i : NoWaitFlowShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsFlowShopSchedule i σ ∧
    ∀ j p q, q.1 = p.1 + 1 → σ q j = σ p j + taskLength i p j

open Classical in
/-- NO-WAIT FLOW-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def noWaitFlowShopSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NoWaitFlowShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ NoWaitFlowShopSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
