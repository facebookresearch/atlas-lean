/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, makespan (`P2;S1|s_i=1|Cmax`)
is NP-complete

Source:
S. A. Kravchenko and F. Werner, "Parallel machine scheduling problems with a single server",
Mathematical and Computer Modelling 26 (1997), 1-11, doi:10.1016/S0895-7177(97)00236-7;
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common
server", Discrete Applied Mathematics 102 (2000), 223-243,
doi:10.1016/S0166-218X(99)00206-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|s_i=1|C_max`, NP-hard and
maximal pseudo-polynomially solvable, citing Hall et al. 2000 and Kravchenko and Werner 1997).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesUnitSetupMakespan

open MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
  (SingleServerTwoMachinesEqualSetupMakespanInstance
    SingleServerTwoMachinesEqualSetupMakespanFeasible)

/-!
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, makespan, is NP-complete

INSTANCE: `m = 2` identical parallel machines, each processing at most one job at a time; jobs
`1, …, n`, job `i` with a processing time `p_i ∈ ℤ₀⁺`; and a bound `K`. Each job is processed on
one machine, without interruption. Immediately before its processing, job `i` must be loaded
(set up) on its machine, which takes the setup time `s_i = 1`; during the setup both the machine
and the server are occupied, and all setups are done by a single server, which handles at most
one job at a time. QUESTION: is there a feasible schedule whose makespan `max_i C_i` is at most
`K`, where `C_i` is the completion time of job `i`?

This is `P2;S1|s_i=1|C_max` in the notation of Kravchenko and Werner, Hall et al. and the
Brucker-Knust classification, the restriction of `P2;S1|s_i=s|C_max`
(`SingleServerTwoMachinesEqualSetupMakespanWanted`) to the setup time `s = 1`. The instance
`(s, p, K)` (jobs listed one per entry by their processing times), the parent well-formedness
condition and the question (a `SingleServerTwoMachinesEqualSetupMakespan.IsSingleServerSchedule`
on two machines completing every job by `K`) are that module's; the restriction `s = 1` is added
to `WellFormed`. Binary encoding of all numbers: Kravchenko and Werner prove NP-hardness and
give a pseudo-polynomial algorithm, so the problem is NP-complete in the ordinary sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed `P2;S1|s_i=s|C_max` instance whose
common setup time is `s = 1`. -/
def WellFormed (i : SingleServerTwoMachinesEqualSetupMakespanInstance) : Prop :=
  SingleServerTwoMachinesEqualSetupMakespan.WellFormed i ∧ i.1 = 1

open Classical in
/-- `P2;S1|s_i=1|Cmax` as a decision problem over bitstrings. -/
noncomputable def singleServerTwoMachinesUnitSetupMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleServerTwoMachinesEqualSetupMakespanInstance) x with
  | some i => decide (WellFormed i ∧ SingleServerTwoMachinesEqualSetupMakespanFeasible i)
  | none => false

/-- **TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, makespan (`P2;S1|s_i=1|Cmax`) is
NP-complete.** Source: Kravchenko and Werner (1997); Hall, Potts and Sriskandarajah (2000); as
recorded in the Brucker-Knust classification. -/
public theorem_wanted singleServerTwoMachinesUnitSetupMakespan_npComplete :
    singleServerTwoMachinesUnitSetupMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L singleServerTwoMachinesUnitSetupMakespanDec

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesUnitSetupMakespan
