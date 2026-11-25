/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal setups, total completion time
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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WantedExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
  (SingleServerTwoMachinesEqualSetupMakespanInstance WellFormed IsSingleServerSchedule)

/-!
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal setups, total completion time, is
NP-complete

INSTANCE: `m = 2` identical parallel machines, each processing at most one job at a time; jobs
`1, …, n`, job `i` with a processing time `p_i ∈ ℤ₀⁺`; a setup time `s ∈ ℤ₀⁺`, the same for all
jobs; and a bound `K`. Each job is processed on one machine, without interruption. Immediately
before its processing, job `i` must be loaded (set up) on its machine, which takes the setup time
`s_i = s`; during the setup both the machine and the server are occupied, and all setups are
done by a single server, which handles at most one job at a time. QUESTION: is there a feasible
schedule whose total completion time `Σ_i C_i` is at most `K`, where `C_i` is the completion
time of job `i`?

This is `P2;S1|s_i=s|ΣC_i` in the notation of Hall et al. and the Brucker-Knust classification.
The instance `(s, p, K)` (jobs listed one per entry by their processing times) and its
well-formedness are those of `SingleServerTwoMachinesEqualSetupMakespan` (`P2;S1|s_i=s|C_max`),
and a schedule is a `SingleServerTwoMachinesEqualSetupMakespan.IsSingleServerSchedule` on two
machines with setup time `s` for every job: job `j` is set up on machine `μ j` during
`[t j, t j + s)` and processed there until `C_j = t j + s + p_j`. Start times are natural numbers
as in that module (rounding all start times down keeps a schedule feasible and increases no
completion time). Membership in NP is the certificate argument: the machine and the setup start
time (at most `K`) of every job, checked pairwise in polynomial time. Binary encoding of all
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

/-- **TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal setups, total completion time
(`P2;S1|s_i=s|ΣC_i`) is NP-complete.** Source: Hall, Potts and Sriskandarajah (2000), as
recorded in the Brucker-Knust classification. -/
public theorem_wanted singleServerTwoMachinesEqualSetupTotalCompletion_npComplete :
    singleServerTwoMachinesEqualSetupTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleServerTwoMachinesEqualSetupTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupTotalCompletion
