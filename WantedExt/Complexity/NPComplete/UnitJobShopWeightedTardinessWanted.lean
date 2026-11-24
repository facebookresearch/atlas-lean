/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# J2|p_ij=1|Σw_jT_j (two-machine unit-time job shop, total weighted tardiness) is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85 (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
recorded in P. Brucker and S. Knust, "Complexity results for scheduling problems", table
"Job-shop problems without preemption" (minimal NP-hard in the strong sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitJobShopWeightedTardiness

/-!
# J2|p_ij=1|Σw_jT_j is NP-complete

INSTANCE: two machines `M₁, M₂` in a job shop and jobs `j`, each a chain of `nⱼ ≥ 1` operations
`O_{j1}, …, O_{jnⱼ}` of unit length; operation `O_{jk}` is processed on a given machine
`μ_{jk}`, consecutive operations of a job use different machines, and `O_{j,k+1}` cannot start
before `O_{jk}` is completed; each machine processes at most one operation at a time; job `j` has a
due date `dⱼ ∈ ℤ₀⁺` and a weight `wⱼ ∈ ℤ₀⁺`;
and a bound `K`.
QUESTION: is there a feasible schedule with the total weighted tardiness `Σⱼ wⱼ max(0, Cⱼ - dⱼ)` at
most `K`, where `Cⱼ` is the completion time
of job `j` (of its last operation)?

This is JOB-SHOP SCHEDULING ([SS18], `JobShopSchedulingWanted`) with `m = 2` processors, every
task of length `1`, and the deadline replaced by a bound on the total weighted tardiness `Σⱼ wⱼ
max(0, Cⱼ - dⱼ)`. The instance pairs the
parent's instance `(m, tasks per job as (l(t), p(t)), K)` (its last component is the bound `K`)
with one pair `(dⱼ, wⱼ)` per job. `WellFormed` asks for `m = 2`, every job nonempty with every task
of
length `1` on processor `1` or `2`, consecutive tasks of a job on different processors, and one
pair per job; all numbers, `K` included, may be `0`. The schedule conditions are the parent's
(`JobShopScheduling.Task`, `taskLength`, `taskProcessor`): on each processor tasks get distinct
start times and a task starting after another starts no earlier than that one ends (for unit
tasks: at most one operation at a time), and each task of a job starts no earlier than the
previous task of the job ends; `C j` is the end of the last task of job `j`. Operations are
listed one by one, so the instance size counts every operation (Timkovsky's results used here
are NP-hardness in the strong sense). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the parent instance (`m`, each job's tasks `(l(t), p(t))`, the bound `K`) and
one pair `(dⱼ, wⱼ)` (due date, weight) per job. -/
abbrev UnitJobShopWeightedTardinessInstance :=
  JobShopScheduling.JobShopSchedulingInstance × List (ℕ × ℕ)

/-- Well-formedness: `m = 2`, every job is a nonempty chain of unit tasks on processors `1`, `2`
with consecutive tasks on different processors, and one pair per job. -/
def WellFormed (i : UnitJobShopWeightedTardinessInstance) : Prop :=
  i.1.1 = 2 ∧ (∀ job ∈ i.1.2.1, job ≠ []) ∧
    (∀ job ∈ i.1.2.1, ∀ t ∈ job, t.1 = 1 ∧ 1 ≤ t.2 ∧ t.2 ≤ 2) ∧
    (∀ job ∈ i.1.2.1, job.IsChain fun t t' => t.2 ≠ t'.2) ∧ i.2.length = i.1.2.1.length

/-- Some job-shop schedule `σ` of the unit tasks has `Σⱼ wⱼ max(0, Cⱼ - dⱼ) ≤ K` (natural
subtraction `C j - dⱼ` is `max(0, C j - dⱼ)`), where `C j` is the end of the last task of job `j`.
-/
def UnitJobShopWeightedTardinessFeasible (i : UnitJobShopWeightedTardinessInstance) :
    Prop :=
  ∃ σ : JobShopScheduling.Task i.1 → ℕ,
    (∀ t t', JobShopScheduling.taskProcessor i.1 t = JobShopScheduling.taskProcessor i.1 t' →
      σ t = σ t' → t = t') ∧
    (∀ t t', JobShopScheduling.taskProcessor i.1 t = JobShopScheduling.taskProcessor i.1 t' →
      σ t' < σ t → σ t' + JobShopScheduling.taskLength i.1 t' ≤ σ t) ∧
    (∀ j (k k' : Fin (i.1.2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k⟩ + JobShopScheduling.taskLength i.1 ⟨j, k⟩ ≤ σ ⟨j, k'⟩) ∧
    ∃ C : Fin i.1.2.1.length → ℕ,
      (∀ j (k : Fin (i.1.2.1.get j).length), k.1 + 1 = (i.1.2.1.get j).length →
        C j = σ ⟨j, k⟩ + JobShopScheduling.taskLength i.1 ⟨j, k⟩) ∧
      ∑ j : Fin i.1.2.1.length, (i.2.getD j (0, 0)).2 * (C j - (i.2.getD j (0, 0)).1) ≤ i.1.2.2

open Classical in
/-- J2|p_ij=1|Σw_jT_j as a decision
problem over bitstrings. -/
noncomputable def unitJobShopWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitJobShopWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ UnitJobShopWeightedTardinessFeasible i)
  | none => false

/-- **J2|p_ij=1|Σw_jT_j is NP-complete.**
Source: Timkovsky (1998). -/
public theorem_wanted unitJobShopWeightedTardiness_npComplete :
    unitJobShopWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitJobShopWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.UnitJobShopWeightedTardiness
