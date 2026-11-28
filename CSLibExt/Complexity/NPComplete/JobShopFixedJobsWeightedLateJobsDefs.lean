/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOB SHOP WITH `k` JOBS, WEIGHTED NUMBER OF LATE JOBS `J|prec;r_i;n=k|Σw_iU_i`: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.JobShopFixedJobsWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JobShopFixedJobsWeightedLateJobs

open JobShopFixedJobsWeightedTardiness (JobShopFixedJobsWeightedTardinessInstance dueDate weight
  IsSchedule)

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

end MetaMathlibExt.Complexity.NPComplete.JobShopFixedJobsWeightedLateJobs
