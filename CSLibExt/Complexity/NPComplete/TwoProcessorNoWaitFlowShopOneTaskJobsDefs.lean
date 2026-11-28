/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING with one-task jobs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
comment on p. 242 ("NP-complete in the strong sense for m = 2 if jobs with no tasks on the first
processor are allowed [Sahni and Cho, 1977b]");
S. Sahni and Y. Cho, "Complexity of scheduling shops with no wait in process", Mathematics of
Operations Research 4 (1979), 448-457, doi:10.1287/moor.4.4.448.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopOneTaskJobs

/-- An instance: the jobs as triples `(b, l₁, l₂)`, where `b = true` is a job with tasks `t₁[j]`
of length `l₁` and `t₂[j]` of length `l₂`, and `b = false` a job with the single task `t₂[j]` of
length `l₂` (and `l₁ = 0`); and the deadline `D`. -/
abbrev TwoProcessorNoWaitFlowShopOneTaskJobsInstance := List (Bool × ℕ × ℕ) × ℕ

/-- Job `j` has a task on the first processor. -/
def HasFirstTask (i : TwoProcessorNoWaitFlowShopOneTaskJobsInstance) (j : Fin i.1.length) :
    Prop :=
  (i.1.get j).1 = true

/-- The length `l(t₁[j])` of the first task of job `j`. -/
def length₁ (i : TwoProcessorNoWaitFlowShopOneTaskJobsInstance) (j : Fin i.1.length) : ℕ :=
  (i.1.get j).2.1

/-- The length `l(t₂[j])` of the second task of job `j`. -/
def length₂ (i : TwoProcessorNoWaitFlowShopOneTaskJobsInstance) (j : Fin i.1.length) : ℕ :=
  (i.1.get j).2.2

/-- Well-formedness of an instance: a job without a first task records `l₁ = 0`, and `0 < D`. -/
def WellFormed (i : TwoProcessorNoWaitFlowShopOneTaskJobsInstance) : Prop :=
  (∀ j ∈ i.1, j.1 = false → j.2.1 = 0) ∧ 0 < i.2

/-- A no-wait flow-shop schedule meeting the deadline: `σ₁` on the first tasks and `σ₂` on the
second tasks are one-to-one one-processor schedules, every second task ends by `D`, and a job
with two tasks starts its second task exactly when its first task ends. -/
def TwoProcessorNoWaitFlowShopOneTaskJobsFeasible
    (i : TwoProcessorNoWaitFlowShopOneTaskJobsInstance) : Prop :=
  ∃ σ₁ σ₂ : Fin i.1.length → ℕ,
    (∀ j k, HasFirstTask i j → HasFirstTask i k → σ₁ j = σ₁ k → j = k) ∧
    (∀ j k, HasFirstTask i j → HasFirstTask i k → σ₁ k < σ₁ j →
      σ₁ k + length₁ i k ≤ σ₁ j) ∧
    Function.Injective σ₂ ∧
    (∀ j k, σ₂ k < σ₂ j → σ₂ k + length₂ i k ≤ σ₂ j) ∧
    (∀ j, σ₂ j + length₂ i j ≤ i.2) ∧
    ∀ j, HasFirstTask i j → σ₂ j = σ₁ j + length₁ i j

open Classical in
/-- TWO-PROCESSOR NO-WAIT FLOW-SHOP SCHEDULING with one-task jobs as a decision problem over
bitstrings. -/
noncomputable def twoProcessorNoWaitFlowShopOneTaskJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorNoWaitFlowShopOneTaskJobsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorNoWaitFlowShopOneTaskJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopOneTaskJobs
