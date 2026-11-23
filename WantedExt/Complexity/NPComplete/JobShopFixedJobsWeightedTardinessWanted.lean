/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB SHOP WITH `k` JOBS, TOTAL WEIGHTED TARDINESS `J|prec;r_i;n=k|Σw_iT_i` is NP-complete

Source:
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N
(`J3|n=3|C_max` is NP-hard);
M. Middendorf and V. G. Timkovsky, "Transversal graphs for partially ordered sets: sequencing,
merging and scheduling problems", Journal of Combinatorial Optimization 3 (1999), 417-435,
doi:10.1023/A:1009827520712 (pseudo-polynomial algorithm for each fixed `k`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop` (job shop problems without
preemption): `J|prec;r_i;n=k|Σw_iT_i` maximal pseudo-polynomially solvable (Middendorf and
Timkovsky 1999), `J3|n=3|C_max` minimal NP-hard (Sotskov and Shakhlevich 1995).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.JobShopSchedulingWanted
public import WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JobShopFixedJobsWeightedTardiness

open JobShopScheduling (JobShopSchedulingInstance Task taskLength taskProcessor)
open MultipurposeFlowShopPrecedenceMakespan (Prec PrecedenceWellFormed)

/-!
# JOB SHOP WITH `k` JOBS, TOTAL WEIGHTED TARDINESS `J|prec;r_i;n=k|Σw_iT_i` is NP-complete

For a fixed number `k ≥ 3` of jobs:

INSTANCE: machines `M_1, …, M_m` (`m ≥ 1` part of the input) in a job shop and `k` jobs, job
`j` a chain of `n_j ≥ 1` operations `O_j1, …, O_jn_j`; operation `O_jl` is processed on a given
machine `μ_jl` for `p_jl ∈ ℤ₀⁺` time units, consecutive operations of a job use different
machines, and `O_j,l+1` cannot start before `O_jl` is completed; each machine processes at most
one operation at a time; job `j` has a release date `r_j`, a due date `d_j` and a weight `w_j`
(in `ℤ₀⁺`); a precedence relation `→` on the jobs (`i → j`: no operation of `j` starts before
every operation of `i` is completed); and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a feasible
schedule, no job starting before its release date, with total weighted tardiness
`∑_j w_j max(0, C_j - d_j) ≤ K`, where `C_j` is the completion time of job `j` (of its last
operation)?

NP-hardness: with `m = 3`, three jobs, release dates `0`, no precedence pairs, every due date
equal to `y`, every weight `1` and `K = 0`, the question is whether `C_max ≤ y`, which is
`J3|n=3|C_max`, NP-hard by Sotskov and Shakhlevich; for `k > 3` add `k - 3` jobs, each a single
operation of length `0` and weight `0`. Brucker and Knust record `J|prec;r_i;n=k|Σw_iT_i` as
maximal pseudo-polynomially solvable (Middendorf and Timkovsky give a pseudo-polynomial
algorithm for each fixed `k`), so the problem is NP-complete in the ordinary sense; numbers use
the binary encoding. Membership in NP is the certificate argument: shifting operations earlier
while the schedule stays feasible increases no completion time, so every start time can be
taken at most `max_j r_j + ∑ (p_jl + 1)` (the `+ 1` separates operations of length `0`), and
the start times are checked in polynomial time.

Encoding. The machines and jobs are a JOB-SHOP SCHEDULING instance (`JobShopSchedulingWanted`,
Garey and Johnson's [SS18]: `m`, each job's operations listed as pairs `(p_jl, μ_jl)` with
machines numbered `1, …, m`), whose last component is the bound `K` here, and whose tasks, task
lengths and task processors are reused; its well-formedness asks for a positive deadline, so
the shop conditions are stated here without it. Each job has a triple `(r_j, d_j, w_j)`; the
precedence relation is given by its pairs `(i, j)`, which name jobs and form a strict partial
order (`PrecedenceWellFormed` and `Prec` of `MultipurposeFlowShopPrecedenceMakespanWanted`).
The schedule conditions are the job-shop conditions of [SS18] (start times one-to-one on each
machine, an operation starting after another one on its machine waits until that one ends,
operations of a job in order), the first operation of job `j` starting no earlier than `r_j`,
and every operation of `j` starting no earlier than `C_i` when `i → j`. With integer data,
integer start times lose no generality.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a JOB-SHOP SCHEDULING instance (`m`, each job's operations `(p_jl, μ_jl)`, the
bound `K`), one triple `(r_j, d_j, w_j)` (release date, due date, weight) per job, and the
precedence pairs `(i, j)` with `i → j`. -/
abbrev JobShopFixedJobsWeightedTardinessInstance :=
  JobShopSchedulingInstance × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : JobShopFixedJobsWeightedTardinessInstance) : Type := Fin i.1.2.1.length

/-- The release date `r_j` of job `j`. -/
def releaseDate (i : JobShopFixedJobsWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.getD j (0, 0, 0)).1

/-- The due date `d_j` of job `j`. -/
def dueDate (i : JobShopFixedJobsWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.getD j (0, 0, 0)).2.1

/-- The weight `w_j` of job `j`. -/
def weight (i : JobShopFixedJobsWeightedTardinessInstance) (j : Job i) : ℕ :=
  (i.2.1.getD j (0, 0, 0)).2.2

/-- Well-formedness of an instance with `k` jobs: exactly `k` jobs, `m ≥ 1`, every job has at
least one operation, every machine lies in `{1, …, m}`, consecutive operations of a job use
different machines, one triple `(r_j, d_j, w_j)` per job, and the precedence pairs name jobs and
form a strict partial order. -/
def WellFormed (k : ℕ) (i : JobShopFixedJobsWeightedTardinessInstance) : Prop :=
  i.1.2.1.length = k ∧ 0 < i.1.1 ∧ (∀ job ∈ i.1.2.1, job ≠ []) ∧
    (∀ job ∈ i.1.2.1, ∀ t ∈ job, 1 ≤ t.2 ∧ t.2 ≤ i.1.1) ∧
    (∀ job ∈ i.1.2.1, job.IsChain fun t t' => t.2 ≠ t'.2) ∧
    i.2.1.length = i.1.2.1.length ∧ PrecedenceWellFormed i.1.2.1.length i.2.2

/-- `σ` (start times of the operations) is a feasible schedule with job completion times `C`:
the job-shop conditions of [SS18] (start times one-to-one on each machine, an operation starting
after another one on its machine starts no earlier than that one ends, operations of a job in
order), the first operation of each job `j` starting no earlier than `r_j`, `C j` the end of the
last operation of `j`, and every operation of `j` starting no earlier than `C i` when `i → j`. -/
def IsSchedule (i : JobShopFixedJobsWeightedTardinessInstance) (σ : Task i.1 → ℕ)
    (C : Job i → ℕ) : Prop :=
  (∀ t t', taskProcessor i.1 t = taskProcessor i.1 t' → σ t = σ t' → t = t') ∧
    (∀ t t', taskProcessor i.1 t = taskProcessor i.1 t' → σ t' < σ t →
      σ t' + taskLength i.1 t' ≤ σ t) ∧
    (∀ j (l l' : Fin (i.1.2.1.get j).length), l'.1 = l.1 + 1 →
      σ ⟨j, l⟩ + taskLength i.1 ⟨j, l⟩ ≤ σ ⟨j, l'⟩) ∧
    (∀ j (l : Fin (i.1.2.1.get j).length), l.1 = 0 → releaseDate i j ≤ σ ⟨j, l⟩) ∧
    (∀ j (l : Fin (i.1.2.1.get j).length), l.1 + 1 = (i.1.2.1.get j).length →
      C j = σ ⟨j, l⟩ + taskLength i.1 ⟨j, l⟩) ∧
    ∀ a b, Prec i.2.2 a b → ∀ l : Fin (i.1.2.1.get b).length, C a ≤ σ ⟨b, l⟩

/-- Some feasible schedule has total weighted tardiness `∑_j w_j (C_j - d_j)` at most `K`
(natural subtraction: the tardiness `max(0, C_j - d_j)`). -/
def JobShopFixedJobsWeightedTardinessFeasible (i : JobShopFixedJobsWeightedTardinessInstance) :
    Prop :=
  ∃ σ C, IsSchedule i σ C ∧ ∑ j, weight i j * (C j - dueDate i j) ≤ i.1.2.2

open Classical in
/-- `J|prec;r_i;n=k|Σw_iT_i` as a decision problem over bitstrings. -/
noncomputable def jobShopFixedJobsWeightedTardinessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopFixedJobsWeightedTardinessInstance) x with
  | some i => decide (WellFormed k i ∧ JobShopFixedJobsWeightedTardinessFeasible i)
  | none => false

/-- **JOB SHOP WITH `k` JOBS, TOTAL WEIGHTED TARDINESS `J|prec;r_i;n=k|Σw_iT_i` is NP-complete
for every fixed `k ≥ 3`.** Source: Sotskov and Shakhlevich (1995) (`J3|n=3|C_max`); Middendorf
and Timkovsky (1999); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted jobShopFixedJobsWeightedTardiness_npComplete (k : ℕ) (_hk : 3 ≤ k) :
    jobShopFixedJobsWeightedTardinessDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (jobShopFixedJobsWeightedTardinessDec k)

end MetaMathlibExt.Complexity.NPComplete.JobShopFixedJobsWeightedTardiness
