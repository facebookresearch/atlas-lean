/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, total tardiness
(`P2;S1|p_i=1|ΣT_i`) is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitTotalTardiness

open TwoMachineSingleServerUnitWeightedTardiness (IsSingleServerSchedule)

/-!
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, total tardiness

INSTANCE: two identical parallel machines, each processing at most one job at a time; jobs
`1, …, n`, job `i` with processing time `p_i = 1`, a setup time `s_i ∈ ℤ₀⁺` and a due date
`d_i ∈ ℤ₀⁺`; and an integer bound `K`. Each job is processed on one machine, without interruption.
Immediately before its processing, job `i` must be loaded (set up) on its machine, which takes the
setup time `s_i`; all setups are done by a single server, which handles at most one job at a time.
QUESTION: is there a feasible schedule whose total tardiness `Σ_i T_i` is at most `K`, where
`T_i = max(0, C_i - d_i)` and `C_i` is the completion time of job `i`?

This is `P2;S1|p_i=1|ΣT_i` in the notation of Hall, Potts and Sriskandarajah and of the
Brucker-Knust classification. The schedule is
`TwoMachineSingleServerUnitWeightedTardiness.IsSingleServerSchedule`
(`TwoMachineSingleServerUnitWeightedTardinessWanted`, `P2;S1|p_i=1|Σw_iT_i`): each job `i` gets a
machine `μ(i)` and the start time `t(i)` of its setup; the setup occupies the server during
`[t(i), t(i) + s_i)`, and job `i` occupies the machine `μ(i)` during its setup and its processing,
`[t(i), t(i) + s_i + p_i)`, so `C_i = t(i) + s_i + p_i`. Setups of different jobs occupy disjoint
intervals of the server, and different jobs on the same machine occupy disjoint intervals of that
machine. Integral start times lose no generality: for fixed job orders on the server and on the
machines, the earliest start times are integral. Binary encoding of all numbers.

Brucker and Knust list the problem as minimal NP-hard in the ordinary sense, attributing it to Hall
et al. (2000) through the single-machine problem `1||ΣT_i` (Du and Leung). Membership in NP: the
machines and setup start times are a certificate; shifting every setup as early as possible, in the
order of the setup start times and on the same machines, does not increase any completion time, so
some schedule meeting the bound starts every setup by `Σ_i (s_i + 1)`, and the certificate has
polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in `MetaMathlibExt.ComplexityTheory.NP`, plus a
polynomial-time many-one reduction from every language in `NP` (`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, total tardiness
(`P2;S1|p_i=1|ΣT_i`) is NP-complete.** Source: Hall, Potts and Sriskandarajah (2000), as recorded in
the Brucker-Knust classification. -/
public theorem_wanted twoMachineSingleServerUnitTotalTardiness_npComplete :
    twoMachineSingleServerUnitTotalTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineSingleServerUnitTotalTardinessDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitTotalTardiness
