/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal setups, total completion time: definitions
(`P2;S1|s_i=s|ΣC_i`) is NP-complete

Source:
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common
server", Discrete Applied Mathematics 102 (2000), 223-243,
doi:10.1016/S0166-218X(99)00206-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|s_i=s|ΣC_i`, minimal NP-hard
in the strong sense, citing Hall et al. 2000).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
  (SingleServerTwoMachinesEqualSetupMakespanInstance WellFormed IsSingleServerSchedule)

/-- Some single-server schedule on two machines, with setup time `s` for every job, has total
completion time `Σ_j (t j + s + p_j)` at most `K`. -/
def SingleServerTwoMachinesEqualSetupTotalCompletionFeasible
    (i : SingleServerTwoMachinesEqualSetupMakespanInstance) : Prop :=
  ∃ μ : Fin i.2.1.length → Fin 2, ∃ t : Fin i.2.1.length → ℕ,
    IsSingleServerSchedule (fun _ => i.1) i.2.1.get μ t ∧
      (∑ j, (t j + i.1 + i.2.1.get j)) ≤ i.2.2

open Classical in
/-- `P2;S1|s_i=s|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def singleServerTwoMachinesEqualSetupTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleServerTwoMachinesEqualSetupMakespanInstance) x with
  | some i => decide (WellFormed i ∧ SingleServerTwoMachinesEqualSetupTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupTotalCompletion
