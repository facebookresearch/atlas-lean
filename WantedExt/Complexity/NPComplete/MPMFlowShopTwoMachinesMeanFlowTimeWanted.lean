/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-PURPOSE MACHINE FLOW SHOP WITH TWO MACHINES TO MINIMIZE TOTAL COMPLETION TIME
# (`FMPM2||∑ Cᵢ`) is NP-complete

Source:
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117 (the
two-machine flow shop `F2||∑ Cᵢ`, of which this problem is a generalization);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM flow shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `FMPM2||∑ Cᵢ`, minimal NP-hard in the strong sense, Garey et al. (1976)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MPMFlowShopTwoMachinesMeanFlowTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMFlowShopTwoMachinesMeanFlowTime

open MPMFlowShopThreeMachines (MPMFlowShopInstance MPMWellFormed IsMPMFlowShopSchedule)

/-!
# MULTI-PURPOSE MACHINE FLOW SHOP WITH TWO MACHINES TO MINIMIZE TOTAL COMPLETION TIME
# (`FMPM2||∑ Cᵢ`) is NP-complete

INSTANCE: `m = 2` machines `M₁, M₂`; a number `r` of stages with machine sets
`μ₁, …, μᵣ ⊆ {M₁, M₂}`, pairwise different; jobs `J₁, …, Jₙ`, each with exactly `r`
operations `Oᵢ₁, …, Oᵢᵣ` with processing times `pᵢⱼ`; and a bound `K`. QUESTION: can every
operation `Oᵢⱼ` be assigned to one machine of `μⱼ` and given a start time so that each machine
processes at most one operation at a time, `Oᵢⱼ` does not start before `Oᵢ,ⱼ₋₁` is completed
(`j = 2, …, r`), and the sum of the completion times `Cᵢ` of the jobs (of their last
operations) is at most `K`?

This is Brucker's MPM flow shop with `m = 2` machines and the total completion time criterion.
The instance type (a FLOW-SHOP SCHEDULING instance `(r, jobs, K)` and the machine sets), the
MPM well-formedness condition (here with `m = 2`) and the schedule conditions are reused from
`WantedExt.Complexity.NPComplete.MPMFlowShopThreeMachinesWanted`. As in
`WantedExt.Complexity.NPComplete.TwoProcessorFlowShopMeanFlowTimeWanted`, two operations on the
same machine also get different start times (Garey and Johnson's one-processor schedules are
one-to-one); for operations of positive length this already follows from non-overlap, and it
keeps zero-length operations from sharing a start time and lowering the sum.

Choosing `r = 2` and `μⱼ = {Mⱼ}` gives the two-machine flow shop `F2||∑ Cᵢ`: its instances
`(2, jobs, K)` (`TwoProcessorFlowShopMeanFlowTimeWanted`) map to `((2, jobs, K), [[0], [1]])`
with the same schedules, so NP-hardness follows from Garey, Johnson and Sethi (1976), who prove
the minimum mean-flow-time flow shop NP-complete in the strong sense for every `m ≥ 2`.
Membership in NP holds because in a feasible schedule every start time is at most `K` (an
operation starts no later than its job's last operation completes, and each such completion is
at most the sum `∑ Cᵢ ≤ K`), so machine assignments and start times up to `K` are a certificate
of polynomial size. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTI-PURPOSE MACHINE FLOW SHOP WITH TWO MACHINES TO MINIMIZE TOTAL COMPLETION TIME
(`FMPM2||∑ Cᵢ`) is NP-complete.** Source: Garey, Johnson and Sethi (1976) (`F2||∑ Cᵢ`, the
special case `μⱼ = {Mⱼ}`); Brucker (2004) (model). -/
public theorem_wanted mpmFlowShopTwoMachinesMeanFlowTime_npComplete :
    mpmFlowShopTwoMachinesMeanFlowTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mpmFlowShopTwoMachinesMeanFlowTimeDec

end MetaMathlibExt.Complexity.NPComplete.MPMFlowShopTwoMachinesMeanFlowTime
