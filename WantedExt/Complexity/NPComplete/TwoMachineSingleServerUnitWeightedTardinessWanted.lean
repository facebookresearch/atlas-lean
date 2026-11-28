/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, total weighted tardiness
(`P2;S1|p_i=1|Σw_iT_i`) is NP-complete

Source:
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common
server", Discrete Applied Mathematics 102 (2000), 223-243, doi:10.1016/S0166-218X(99)00206-1;
P. Brucker, C. Dhaenens-Flipo, S. Knust, S. A. Kravchenko and F. Werner, "Complexity results
for parallel machine problems with a single server", Journal of Scheduling 5 (2002), 429-457,
doi:10.1002/jos.120 (the model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|p_i=1|Σw_iT_i`, minimal NP-hard
in the strong sense: "Single-machine problem, Hall et al. (2000)");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS5] SEQUENCING TO MINIMIZE WEIGHTED TARDINESS
(the single-machine problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardiness

/-!
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, total weighted tardiness

INSTANCE: two identical parallel machines, each processing at most one job at a time; jobs
`1, …, n`, job `i` with processing time `p_i = 1`, a setup time `s_i ∈ ℤ₀⁺`, a weight
`w_i ∈ ℤ₀⁺` and a due date `d_i ∈ ℤ₀⁺`; and an integer bound `K`. Each job is processed on one
machine, without interruption. Immediately before its processing, job `i` must be loaded (set
up) on its machine, which takes the setup time `s_i`; all setups are done by a single server,
which handles at most one job at a time. QUESTION: is there a feasible schedule whose total
weighted tardiness `Σ_i w_i T_i` is at most `K`, where `T_i = max(0, C_i - d_i)` and `C_i` is
the completion time of job `i`?

This is `P2;S1|p_i=1|Σw_iT_i` in the notation of Hall, Potts and Sriskandarajah, of Brucker et
al. and of the Brucker-Knust classification. A schedule (`IsSingleServerSchedule`) gives each
job `i` a machine `μ(i)` and the start time `t(i)` of its setup: the setup occupies the server
during `[t(i), t(i) + s_i)`, and job `i` occupies the machine `μ(i)` during its setup and its
processing, `[t(i), t(i) + s_i + p_i)`, so `C_i = t(i) + s_i + p_i`. Setups of different jobs
occupy disjoint intervals of the server, and different jobs on the same machine occupy disjoint
intervals of that machine. Integral start times lose no generality: for fixed job orders on the
server and on the machines, the earliest start times are integral. Binary encoding of all
numbers.

Brucker and Knust list the problem as minimal NP-hard in the strong sense, attributing it to
Hall et al. (2000) through the single-machine problem `1||Σw_iT_i` (Garey and Johnson [SS5]).
Membership in NP: the machines and setup start times are a certificate; shifting every setup as
early as possible, in the order of the setup start times and on the same machines, does not
increase any completion time, so some schedule meeting the bound starts every setup by
`Σ_i (s_i + 1)`, and the certificate has polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit processing times, total weighted
tardiness (`P2;S1|p_i=1|Σw_iT_i`) is NP-complete.** Source: Hall, Potts and Sriskandarajah
(2000), as recorded in the Brucker-Knust classification. -/
public theorem_wanted twoMachineSingleServerUnitWeightedTardiness_npComplete :
    twoMachineSingleServerUnitWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineSingleServerUnitWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineSingleServerUnitWeightedTardiness
