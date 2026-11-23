/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, maximum lateness
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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesUnitSetupMaxLateness

open MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
  (IsSingleServerSchedule)

/-!
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, maximum lateness, is NP-complete

INSTANCE: `m = 2` identical parallel machines, each processing at most one job at a time; jobs
`1, …, n` (`n ≥ 1`), job `i` with a processing time `p_i ∈ ℤ₀⁺` and a due date `d_i ∈ ℤ₀⁺`; and
an integer bound `K`. Each job is processed on one machine, without interruption. Immediately
before its processing, job `i` must be loaded (set up) on its machine, which takes the setup time
`s_i = 1`; during the setup both the machine and the server are occupied, and all setups are
done by a single server, which handles at most one job at a time. QUESTION: is there a feasible
schedule whose maximum lateness `max_i (C_i - d_i)` is at most `K`, where `C_i` is the
completion time of job `i`?

This is `P2;S1|s_i=1|L_max` in the notation of Hall et al. and the Brucker-Knust
classification. Jobs are listed one per entry as `(p_i, d_i)`; jobs are `Fin n`. A schedule is a
`SingleServerTwoMachinesEqualSetupMakespan.IsSingleServerSchedule` on two machines with setup
time `1` for every job: job `j` is set up on machine `μ j` during `[t j, t j + 1)` and processed
there until `C_j = t j + 1 + p_j`. Start times are natural numbers as in that module (rounding
all start times down keeps a schedule feasible and increases no completion time). There is at
least one job, since `max_i (C_i - d_i)` is undefined for an empty job set. The bound is an
integer, encoded as a pair `(K⁺, K⁻)` representing `K⁺ - K⁻` as in `ZeroOneILPWanted`, and
`C_j - d_j ≤ K⁺ - K⁻` is stated over `ℕ` as `C_j + K⁻ ≤ d_j + K⁺`. Nonnegative due dates lose no
generality: replacing every `d_i` by `d_i + c` and `K` by `K - c` changes no answer. Membership
in NP is the certificate argument: the machine and the setup start time (at most
`max_j d_j + K⁺`) of every job, checked pairwise in polynomial time. Binary encoding of all
numbers; the source proves NP-hardness in the strong sense, which this statement does not record.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, maximum lateness
(`P2;S1|s_i=1|Lmax`) is NP-complete.** Source: Hall, Potts and Sriskandarajah (2000), as
recorded in the Brucker-Knust classification. -/
public theorem_wanted singleServerTwoMachinesUnitSetupMaxLateness_npComplete :
    singleServerTwoMachinesUnitSetupMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleServerTwoMachinesUnitSetupMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesUnitSetupMaxLateness
