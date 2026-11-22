/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB SHOP WITH `k` JOBS, WEIGHTED NUMBER OF LATE JOBS `J|prec;r_i;n=k|Σw_iU_i` is NP-complete

Source:
Yu. N. Sotskov and N. V. Shakhlevich, "NP-hardness of shop-scheduling problems with three
jobs", Discrete Applied Mathematics 59 (1995), 237-266, doi:10.1016/0166-218X(95)80004-N
(`J3|n=3|C_max` is NP-hard);
M. Middendorf and V. G. Timkovsky, "Transversal graphs for partially ordered sets: sequencing,
merging and scheduling problems", Journal of Combinatorial Optimization 3 (1999), 417-435,
doi:10.1023/A:1009827520712 (pseudo-polynomial algorithm for each fixed `k`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `j_nop` (job shop problems without
preemption): `J|prec;r_i;n=k|Σw_iU_i` maximal pseudo-polynomially solvable (Middendorf and
Timkovsky 1999), `J3|n=3|C_max` minimal NP-hard (Sotskov and Shakhlevich 1995).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.JobShopFixedJobsWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JobShopFixedJobsWeightedLateJobs

open JobShopFixedJobsWeightedTardiness (JobShopFixedJobsWeightedTardinessInstance dueDate weight
  IsSchedule)

/-!
# JOB SHOP WITH `k` JOBS, WEIGHTED NUMBER OF LATE JOBS `J|prec;r_i;n=k|Σw_iU_i` is NP-complete

For a fixed number `k ≥ 3` of jobs:

INSTANCE: machines `M_1, …, M_m` (`m ≥ 1` part of the input) in a job shop and `k` jobs, job
`j` a chain of `n_j ≥ 1` operations `O_j1, …, O_jn_j`; operation `O_jl` is processed on a given
machine `μ_jl` for `p_jl ∈ ℤ₀⁺` time units, consecutive operations of a job use different
machines, and `O_j,l+1` cannot start before `O_jl` is completed; each machine processes at most
one operation at a time; job `j` has a release date `r_j`, a due date `d_j` and a weight `w_j`
(in `ℤ₀⁺`); a precedence relation `→` on the jobs (`i → j`: no operation of `j` starts before
every operation of `i` is completed); and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a feasible
schedule, no job starting before its release date, in which the late jobs (`C_j > d_j`, where
`C_j` is the completion time of job `j`, of its last operation) have total weight at most `K`?

NP-hardness: with `m = 3`, three jobs, release dates `0`, no precedence pairs, every due date
equal to `y`, every weight `1` and `K = 0`, the question is whether `C_max ≤ y`, which is
`J3|n=3|C_max`, NP-hard by Sotskov and Shakhlevich; for `k > 3` add `k - 3` jobs, each a single
operation of length `0` and weight `0`. Brucker and Knust record `J|prec;r_i;n=k|Σw_iU_i` as
maximal pseudo-polynomially solvable (Middendorf and Timkovsky give a pseudo-polynomial
algorithm for each fixed `k`), so the problem is NP-complete in the ordinary sense; numbers use
the binary encoding. Membership in NP is the certificate argument: shifting operations earlier
while the schedule stays feasible increases no completion time, so every start time can be
taken at most `max_j r_j + ∑ (p_jl + 1)` (the `+ 1` separates operations of length `0`), and
the start times are checked in polynomial time.

Encoding. The instance, its well-formedness for `k` jobs and the schedule conditions
(`IsSchedule`: the job-shop conditions of [SS18], release dates, job completion times, and the
precedence constraints) are those of `J|prec;r_i;n=k|Σw_iT_i`
(`JobShopFixedJobsWeightedTardinessWanted`); only the question differs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some feasible schedule has late jobs (`d_j < C_j`) of total weight at most `K`. -/
def JobShopFixedJobsWeightedLateJobsFeasible (i : JobShopFixedJobsWeightedTardinessInstance) :
    Prop :=
  ∃ σ C, IsSchedule i σ C ∧
    ∑ j ∈ Finset.univ.filter (fun j => dueDate i j < C j), weight i j ≤ i.1.2.2

open Classical in
/-- `J|prec;r_i;n=k|Σw_iU_i` as a decision problem over bitstrings. -/
noncomputable def jobShopFixedJobsWeightedLateJobsDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JobShopFixedJobsWeightedTardinessInstance) x with
  | some i => decide (JobShopFixedJobsWeightedTardiness.WellFormed k i ∧
      JobShopFixedJobsWeightedLateJobsFeasible i)
  | none => false

/-- **JOB SHOP WITH `k` JOBS, WEIGHTED NUMBER OF LATE JOBS `J|prec;r_i;n=k|Σw_iU_i` is
NP-complete for every fixed `k ≥ 3`.** Source: Sotskov and Shakhlevich (1995)
(`J3|n=3|C_max`); Middendorf and Timkovsky (1999); Brucker and Knust, *Complexity results for
scheduling problems*. -/
public theorem_wanted jobShopFixedJobsWeightedLateJobs_npComplete (k : ℕ) (_hk : 3 ≤ k) :
    jobShopFixedJobsWeightedLateJobsDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (jobShopFixedJobsWeightedLateJobsDec k)

end MetaMathlibExt.Complexity.NPComplete.JobShopFixedJobsWeightedLateJobs
