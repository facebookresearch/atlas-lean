/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal processing times, makespan
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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerEqualProcessingMakespan

open TwoMachineSingleServerUnitWeightedTardiness (IsSingleServerSchedule)

/-!
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal processing times, makespan

INSTANCE: two identical parallel machines, each processing at most one job at a time; a processing
time `p ∈ ℤ⁺`; jobs `1, …, n`, job `i` with processing time `p_i = p` and a setup time `s_i ∈ ℤ₀⁺`;
and an integer bound `K`. Each job is processed on one machine, without interruption. Immediately
before its processing, job `i` must be loaded (set up) on its machine, which takes the setup time
`s_i`; all setups are done by a single server, which handles at most one job at a time. QUESTION: is
there a feasible schedule whose makespan `max_i C_i` is at most `K`, where `C_i` is the completion
time of job `i`?

This is `P2;S1|p_i=p|C_max` in the notation of Brucker et al. and of the Brucker-Knust
classification. The schedule is `TwoMachineSingleServerUnitWeightedTardiness.IsSingleServerSchedule`
(`TwoMachineSingleServerUnitWeightedTardinessWanted`, `P2;S1|p_i=1|Σw_iT_i`): each job `i` gets a
machine `μ(i)` and the start time `t(i)` of its setup; the setup occupies the server during
`[t(i), t(i) + s_i)`, and job `i` occupies the machine `μ(i)` during its setup and its processing,
`[t(i), t(i) + s_i + p_i)`, so `C_i = t(i) + s_i + p_i`. Setups of different jobs occupy disjoint
intervals of the server, and different jobs on the same machine occupy disjoint intervals of that
machine. Integral start times lose no generality: for fixed job orders on the server and on the
machines, the earliest start times are integral. Binary encoding of all numbers.

Brucker et al. prove the problem NP-hard, and Brucker and Knust list it as minimal NP-hard in the
ordinary sense. Membership in NP: the machines and setup start times are a certificate; every setup
start time is at most `C_i ≤ K`, so the certificate has polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in `MetaMathlibExt.ComplexityTheory.NP`, plus a
polynomial-time many-one reduction from every language in `NP` (`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO PARALLEL MACHINES WITH A SINGLE SERVER, equal processing times, makespan
(`P2;S1|p_i=p|C_max`) is NP-complete.** Source: Brucker, Dhaenens-Flipo, Knust, Kravchenko and
Werner (2002). -/
public theorem_wanted twoMachineSingleServerEqualProcessingMakespan_npComplete :
    twoMachineSingleServerEqualProcessingMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineSingleServerEqualProcessingMakespanDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerEqualProcessingMakespan
