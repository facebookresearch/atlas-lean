/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, maximum lateness: definitions
(`P2;S1|s_i=1|Lmax`) is NP-complete

Source:
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common
server", Discrete Applied Mathematics 102 (2000), 223-243,
doi:10.1016/S0166-218X(99)00206-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|s_i=1|L_max`, minimal NP-hard
in the strong sense, citing Hall et al. 2000).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesUnitSetupMaxLateness

open MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
  (IsSingleServerSchedule)

/-- An instance: the jobs, job `j` being the `j`-th pair `(p_j, d_j)` of its processing time and
its due date, and the bound `K` as a pair `(K⁺, K⁻)` with `K = K⁺ - K⁻`. -/
abbrev SingleServerTwoMachinesUnitSetupMaxLatenessInstance := List (ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: there is at least one job. -/
def WellFormed (i : SingleServerTwoMachinesUnitSetupMaxLatenessInstance) : Prop :=
  i.1 ≠ []

/-- Some single-server schedule on two machines, with setup time `1` for every job, completes
every job `j` with lateness `C_j - d_j ≤ K⁺ - K⁻`, that is `t j + 1 + p_j + K⁻ ≤ d_j + K⁺`. -/
def SingleServerTwoMachinesUnitSetupMaxLatenessFeasible
    (i : SingleServerTwoMachinesUnitSetupMaxLatenessInstance) : Prop :=
  ∃ μ : Fin i.1.length → Fin 2, ∃ t : Fin i.1.length → ℕ,
    IsSingleServerSchedule (fun _ => 1) (fun j => (i.1.get j).1) μ t ∧
      ∀ j, t j + 1 + (i.1.get j).1 + i.2.2 ≤ (i.1.get j).2 + i.2.1

open Classical in
/-- `P2;S1|s_i=1|Lmax` as a decision problem over bitstrings. -/
noncomputable def singleServerTwoMachinesUnitSetupMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleServerTwoMachinesUnitSetupMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ SingleServerTwoMachinesUnitSetupMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesUnitSetupMaxLateness
