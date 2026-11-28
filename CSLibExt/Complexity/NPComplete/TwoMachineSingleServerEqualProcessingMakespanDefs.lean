/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal processing times, makespan: definitions
(`P2;S1|p_i=p|C_max`) is NP-complete

Source:
P. Brucker, C. Dhaenens-Flipo, S. Knust, S. A. Kravchenko and F. Werner, "Complexity results for
parallel machine problems with a single server", Journal of Scheduling 5 (2002), 429-457,
doi:10.1002/jos.120;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück, class
"Parallel machine problems with a single server" (`P2;S1|p_i=p|C_max`, minimal NP-hard in the
ordinary sense, citing Brucker et al. 2002).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerEqualProcessingMakespan

open TwoMachineSingleServerUnitWeightedTardiness (IsSingleServerSchedule)

/-- An instance `(p, s, K)`: the common processing time `p`, the setup times `s_j` of the jobs
`0, …, n - 1` (`n` is the length of the list), and the bound `K`. -/
abbrev TwoMachineSingleServerEqualProcessingMakespanInstance := ℕ × List ℕ × ℕ

/-- Well-formedness of an instance: the common processing time is positive. -/
def WellFormed (i : TwoMachineSingleServerEqualProcessingMakespanInstance) : Prop :=
  0 < i.1

/-- Some schedule on two machines with a single server and processing times `p` completes every job
by `K`: `C_j = t j + s_j + p ≤ K`. -/
def TwoMachineSingleServerEqualProcessingMakespanFeasible
    (i : TwoMachineSingleServerEqualProcessingMakespanInstance) : Prop :=
  ∃ μ : Fin i.2.1.length → Fin 2, ∃ t : Fin i.2.1.length → ℕ,
    IsSingleServerSchedule 2 (fun j => i.2.1.get j) (fun _ => i.1) μ t ∧
      ∀ j, t j + i.2.1.get j + i.1 ≤ i.2.2

open Classical in
/-- `P2;S1|p_i=p|C_max` as a decision problem over bitstrings. -/
noncomputable def twoMachineSingleServerEqualProcessingMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineSingleServerEqualProcessingMakespanInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineSingleServerEqualProcessingMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerEqualProcessingMakespan
