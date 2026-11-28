/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, total tardiness
(`P2;S1|p_i=1|ΣT_i`): definitions

Source:
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common server",
Discrete Applied Mathematics 102 (2000), 223-243, doi:10.1016/S0166-218X(99)00206-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück, class
"Parallel machine problems with a single server" (`P2;S1|p_i=1|ΣT_i`, minimal NP-hard in the
ordinary sense: "Single-machine problem, Hall et al. (2000)");
J. Du and J. Y.-T. Leung, "Minimizing total tardiness on one machine is NP-hard", Mathematics of
Operations Research 15 (1990), 483-495, doi:10.1287/moor.15.3.483 (the single-machine problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitTotalTardiness

open TwoMachineSingleServerUnitWeightedTardiness (IsSingleServerSchedule)

/-- An instance `(jobs, K)`: job `j` is the `j`-th pair `(s_j, d_j)` of setup time and due date
(every processing time is `1`), and `K` is the bound. -/
abbrev TwoMachineSingleServerUnitTotalTardinessInstance := List (ℕ × ℕ) × ℕ

/-- Some schedule on two machines with a single server and unit processing times has total tardiness
`Σ_j max(0, C_j - d_j)` at most `K`, where `C_j = t j + s_j + 1` (natural-number subtraction
truncates at `0`). -/
def TwoMachineSingleServerUnitTotalTardinessFeasible
    (i : TwoMachineSingleServerUnitTotalTardinessInstance) : Prop :=
  ∃ μ : Fin i.1.length → Fin 2, ∃ t : Fin i.1.length → ℕ,
    IsSingleServerSchedule 2 (fun j => (i.1.get j).1) (fun _ => 1) μ t ∧
      (∑ j, (t j + (i.1.get j).1 + 1 - (i.1.get j).2)) ≤ i.2

open Classical in
/-- `P2;S1|p_i=1|ΣT_i` as a decision problem over bitstrings. -/
noncomputable def twoMachineSingleServerUnitTotalTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineSingleServerUnitTotalTardinessInstance) x with
  | some i => decide (TwoMachineSingleServerUnitTotalTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitTotalTardiness
