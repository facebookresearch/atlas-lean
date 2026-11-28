/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, weighted number of late jobs: definitions
(`P2;S1|p_i=1|Σw_iU_i`) is NP-complete

Source:
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common server",
Discrete Applied Mathematics 102 (2000), 223-243, doi:10.1016/S0166-218X(99)00206-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück, class
"Parallel machine problems with a single server" (`P2;S1|p_i=1|Σw_iU_i`, minimal NP-hard in the
ordinary sense: "Single-machine problem, Hall et al. (2000)");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS3] SEQUENCING TO MINIMIZE TARDY TASK WEIGHT (the
single-machine problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedLateJobs

open TwoMachineSingleServerUnitWeightedTardiness
  (TwoMachineSingleServerUnitInstance IsSingleServerSchedule)

/-- Some schedule on two machines with a single server and unit processing times has total weight of
late jobs at most `K`: the sum of `w_j` over the jobs with `C_j = t j + s_j + 1 > d_j` is at most
`K`. -/
def TwoMachineSingleServerUnitWeightedLateJobsFeasible
    (i : TwoMachineSingleServerUnitInstance) : Prop :=
  ∃ μ : Fin i.1.length → Fin 2, ∃ t : Fin i.1.length → ℕ,
    IsSingleServerSchedule 2 (fun j => (i.1.get j).1) (fun _ => 1) μ t ∧
      (∑ j ∈ Finset.univ.filter (fun j => (i.1.get j).2.2 < t j + (i.1.get j).1 + 1),
        (i.1.get j).2.1) ≤ i.2

open Classical in
/-- `P2;S1|p_i=1|Σw_iU_i` as a decision problem over bitstrings. -/
noncomputable def twoMachineSingleServerUnitWeightedLateJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineSingleServerUnitInstance) x with
  | some i => decide (TwoMachineSingleServerUnitWeightedLateJobsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedLateJobs
