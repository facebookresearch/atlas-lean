/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT UNIT-TIME TWO-MACHINE JOB SHOP (J2|p_ij = 1; r_i; no-wait|ΣC_i): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopReleaseTotalCompletion

open JobShopScheduling (Task taskLength taskProcessor)

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

end MetaMathlibExt.Complexity.NPComplete.TwoMachineUnitNoWaitJobShopReleaseTotalCompletion
