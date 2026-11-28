/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT UNIT-TIME TWO-MACHINE JOB SHOP (J2|p_ij = 1; r_i; no-wait|ΣC_i) is NP-complete

Source:
V. G. Timkovsky, "Is a unit-time job shop not easier than identical parallel machines?",
Discrete Applied Mathematics 85(2) (1998), 149-162, doi:10.1016/S0166-218X(98)00032-8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Job-shop problems with nowait",
which lists `J2|p_ij = 1; r_i; no-wait|ΣC_i` as minimal NP-hard in the strong sense with the
attribution to Timkovsky (1998);
P. Brucker, *Scheduling Algorithms*, Springer, Section 6.4 (the job-shop model).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopReleaseTotalCompletion

open JobShopScheduling (Task taskLength taskProcessor)

/-!
# NO-WAIT UNIT-TIME TWO-MACHINE JOB SHOP (J2|p_ij = 1; r_i; no-wait|ΣC_i) is NP-complete

INSTANCE: `m = 2` machines `M_1, M_2` in a job shop; jobs `1, …, n`, each job `i` a chain of
`n_i ≥ 1` operations `O_i1, …, O_in_i`, where `O_ij` must be processed on a given machine
`μ_ij ∈ {M_1, M_2}` for `p_ij = 1` time unit, consecutive operations of a job use different
machines (`μ_ij ≠ μ_i,j+1`), and `O_i,j+1` cannot start before `O_ij` is completed; a release
date `r_i ∈ ℤ₀⁺` for each job `i`, before which no operation of `i` starts; and a bound `K`.
Each machine processes at most one operation at a time. No-wait: each operation of a job starts
exactly when the preceding operation of the same job is completed. QUESTION: is there a
feasible schedule whose total completion time `Σ_i C_i` is at most `K`, where `C_i` is the
completion time of job `i` (that of its last operation)?

This is the job-shop model of `JobShopSchedulingDefs` (Garey and Johnson's [SS18]), whose
task type `JobShopScheduling.Task`, `JobShopScheduling.taskLength`,
`JobShopScheduling.taskProcessor` and `JobShopScheduling.WellFormed` are reused through
`toJobShop`, specialized to two machines and unit processing times, with release dates, the
no-wait condition, and the total completion time `Σ_i C_i` in place of the common deadline.
`toJobShop` sets the parent's deadline component to `1`; it enters only the parent's
well-formedness conjunct `0 < D` and no condition used here. Machines are numbered `1` and `2`
as in the parent. Machine conflicts are stated with the parent's one-processor schedule
conditions ([SS1]: one-to-one start times on each machine, and an operation starting later on a
machine starts no earlier than the other one finishes). With unit processing times and integer
release dates, integer start times lose no generality. Numbers use the binary encoding; the
operations of every job are listed explicitly.

Brucker and Knust classify the problem as NP-hard in the strong sense (Timkovsky 1998), so it
stays NP-hard when every job has polynomially many operations listed one by one, as here.
Membership in NP is the certificate argument: the start times of the listed operations, each
below `K` in a yes-instance, are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs (job `i` is the pair of its operation list `O_i1, …, O_in_i`, each
operation given as the pair `(p_ij, μ_ij)` of its processing time and its machine, and its
release date `r_i`) and the bound `K`. -/
abbrev TwoMachineUnitNoWaitJobShopReleaseTotalCompletionInstance :=
  List (List (ℕ × ℕ) × ℕ) × ℕ

/-- The two-machine job-shop instance of `JobShopSchedulingDefs` with the same jobs (and
deadline component `1`, which no condition below uses). -/
abbrev toJobShop (i : TwoMachineUnitNoWaitJobShopReleaseTotalCompletionInstance) :
    JobShopScheduling.JobShopSchedulingInstance :=
  (2, i.1.map Prod.fst, 1)

/-- The release date `r_j` of job `j`. -/
def releaseDate (i : TwoMachineUnitNoWaitJobShopReleaseTotalCompletionInstance)
    (j : Fin (toJobShop i).2.1.length) : ℕ :=
  (i.1.get (Fin.cast (by simp) j)).2

/-- The completion time `C_j` of job `j` under start times `σ`: the latest completion time of its
operations (by the chain constraints, that of its last operation). -/
def completionTime (i : TwoMachineUnitNoWaitJobShopReleaseTotalCompletionInstance)
    (σ : Task (toJobShop i) → ℕ) (j : Fin (toJobShop i).2.1.length) : ℕ :=
  Finset.univ.sup fun k : Fin ((toJobShop i).2.1.get j).length =>
    σ ⟨j, k⟩ + taskLength (toJobShop i) ⟨j, k⟩

/-- Well-formedness of an instance: the jobs form a well-formed two-machine job shop
(`JobShopScheduling.WellFormed` of `toJobShop`: every job has at least one operation, every
machine is `1` or `2`, and consecutive operations of a job use different machines), and every
processing time is `1`. -/
def WellFormed (i : TwoMachineUnitNoWaitJobShopReleaseTotalCompletionInstance) : Prop :=
  JobShopScheduling.WellFormed (toJobShop i) ∧ ∀ job ∈ i.1, ∀ t ∈ job.1, t.1 = 1

/-- There is a no-wait schedule meeting the bound: start times `σ` that are one-to-one on the
operations of each machine, such that an operation of a machine starting after another
operation `t'` of that machine starts no earlier than `t'` finishes, each operation of a job
after the first starts exactly when the previous operation of that job finishes, no operation
of job `j` starts before `r_j`, and the total completion time `Σ_j C_j` is at most `K`. -/
def TwoMachineUnitNoWaitJobShopReleaseTotalCompletionFeasible
    (i : TwoMachineUnitNoWaitJobShopReleaseTotalCompletionInstance) : Prop :=
  ∃ σ : Task (toJobShop i) → ℕ,
    (∀ t t', taskProcessor (toJobShop i) t = taskProcessor (toJobShop i) t' →
      σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor (toJobShop i) t = taskProcessor (toJobShop i) t' → σ t' < σ t →
      σ t' + taskLength (toJobShop i) t' ≤ σ t) ∧
    (∀ j (k k' : Fin ((toJobShop i).2.1.get j).length), k'.1 = k.1 + 1 →
      σ ⟨j, k'⟩ = σ ⟨j, k⟩ + taskLength (toJobShop i) ⟨j, k⟩) ∧
    (∀ j (k : Fin ((toJobShop i).2.1.get j).length), releaseDate i j ≤ σ ⟨j, k⟩) ∧
    ∑ j, completionTime i σ j ≤ i.2

open Classical in
/-- `J2|p_ij = 1; r_i; no-wait|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def twoMachineUnitNoWaitJobShopReleaseTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineUnitNoWaitJobShopReleaseTotalCompletionInstance) x with
  | some i =>
      decide (WellFormed i ∧ TwoMachineUnitNoWaitJobShopReleaseTotalCompletionFeasible i)
  | none => false

/-- **`J2|p_ij = 1; r_i; no-wait|ΣC_i` is NP-complete.** Source: Timkovsky (1998); Brucker and
Knust, *Complexity results for scheduling problems* (strongly NP-hard); membership in NP is the
certificate argument in the module docstring. -/
public theorem_wanted twoMachineUnitNoWaitJobShopReleaseTotalCompletion_npComplete :
    twoMachineUnitNoWaitJobShopReleaseTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineUnitNoWaitJobShopReleaseTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopReleaseTotalCompletion
