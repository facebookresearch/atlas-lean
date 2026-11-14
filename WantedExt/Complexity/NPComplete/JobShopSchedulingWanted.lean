/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB-SHOP SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS18] JOB-SHOP
SCHEDULING (with the definition of one-processor schedules in [SS1]);
M. R. Garey, D. S. Johnson, and R. Sethi, "The complexity of flowshop and
jobshop scheduling", Mathematics of Operations Research 1 (1976), 117-129,
doi:10.1287/moor.1.2.117.
-/
module

public import Batteries.Data.List.Basic
public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-!
# JOB-SHOP SCHEDULING is NP-complete

INSTANCE: a number `m ∈ ℤ⁺` of processors, a set `J` of jobs, each job `j ∈ J` consisting of
an ordered collection of tasks `t_k[j]`, `1 ≤ k ≤ n_j`, for each such task `t` a length
`l(t) ∈ ℤ₀⁺` and a processor `p(t) ∈ {1, 2, …, m}`, where `p(t_k[j]) ≠ p(t_{k+1}[j])` for all
`j ∈ J` and `1 ≤ k < n_j`, and a deadline `D ∈ ℤ⁺`.
QUESTION: is there a job-shop schedule for `J` that meets the overall deadline, i.e., a
collection of one-processor schedules `σᵢ` mapping `{t : p(t) = i}` into `ℤ₀⁺`, `1 ≤ i ≤ m`,
such that `σᵢ(t) > σᵢ(t')` implies `σᵢ(t) ≥ σᵢ(t') + l(t')`, such that
`σ(t_{k+1}[j]) ≥ σ(t_k[j]) + l(t_k[j])` for all `j ∈ J` and `1 ≤ k < n_j`, and such that
`σ(t_{n_j}[j]) + l(t_{n_j}[j]) ≤ D` for all `j ∈ J`?

A one-processor schedule [SS1] is one-to-one. The `σᵢ` have disjoint domains, so they are
represented by one function `σ` on all tasks, required to be one-to-one on the tasks of each
processor. Garey and Johnson print the machine constraint of [SS18] as
"`σᵢ(t) > σᵢ(t')` implies `σᵢ(t) ≥ σᵢ(t') + l(t)`"; that is a misprint for `l(t')`, the
one-processor schedule condition of [SS1] (a task starting later must wait until the earlier
task `t'` finishes), which is what is stated here. Task positions are numbered from `0` below.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `m` of processors, the jobs (job `j` is the list of its tasks
`t_1[j], …, t_{n_j}[j]` in order, each task given as the pair `(l(t), p(t))` of its length and
its processor), and the deadline `D`. -/
abbrev JobShopSchedulingInstance := ℕ × List (List (ℕ × ℕ)) × ℕ

/-- Well-formedness of an instance: `m ∈ ℤ⁺`, every task's processor lies in
`{1, …, m}`, consecutive tasks of a job use different processors (`List.IsChain`), and
`D ∈ ℤ⁺`. -/
def WellFormed (i : JobShopSchedulingInstance) : Prop :=
  0 < i.1 ∧ (∀ job ∈ i.2.1, ∀ t ∈ job, 1 ≤ t.2 ∧ t.2 ≤ i.1) ∧
    (∀ job ∈ i.2.1, job.IsChain fun t t' => t.2 ≠ t'.2) ∧ 0 < i.2.2

/-- A task `t_k[j]` of the instance: a job `j` and a position `k < n_j` in its task
sequence. -/
abbrev Task (i : JobShopSchedulingInstance) : Type :=
  (j : Fin i.2.1.length) × Fin (i.2.1.get j).length

/-- The length `l(t)` of a task. -/
def taskLength (i : JobShopSchedulingInstance) (t : Task i) : ℕ :=
  ((i.2.1.get t.1).get t.2).1

/-- The processor `p(t)` of a task. -/
def taskProcessor (i : JobShopSchedulingInstance) (t : Task i) : ℕ :=
  ((i.2.1.get t.1).get t.2).2

/-- There is a job-shop schedule meeting the deadline: start times `σ` that are one-to-one
on the tasks of each processor, such that a task of a processor starting after another task
`t'` of that processor starts no earlier than `t'` finishes, each task of a job starts no
earlier than the previous task of that job finishes, and the last task of every job
finishes by `D`. -/
def JobShopSchedulingFeasible (i : JobShopSchedulingInstance) : Prop :=
  ∃ σ : Task i → ℕ,
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i t = taskProcessor i t' → σ t' < σ t →
      σ t' + taskLength i t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + taskLength i ⟨j, k⟩ ≤ σ ⟨j, k'⟩) ∧
    ∀ j (k : Fin (i.2.1.get j).length), k.1 + 1 = (i.2.1.get j).length →
      σ ⟨j, k⟩ + taskLength i ⟨j, k⟩ ≤ i.2.2

open Classical in
/-- JOB-SHOP SCHEDULING as a decision problem over bitstrings. -/
noncomputable def jobShopSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ JobShopSchedulingFeasible i)
  | none => false

/-- **JOB-SHOP SCHEDULING is NP-complete.** Source: Garey and Johnson (1979), [SS18];
Garey, Johnson, and Sethi (1976). -/
public theorem_wanted jobShopScheduling_npComplete :
    jobShopSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L jobShopSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.JobShopScheduling
