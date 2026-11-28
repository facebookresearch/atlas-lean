/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTI-PURPOSE MACHINE FLOW SHOP WITH THREE MACHINES (`FMPM3||C_max`) is NP-complete

Source:
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129, doi:10.1287/moor.1.2.117 (the
three-machine flow shop `F3||C_max`, of which this problem is a generalization);
P. Brucker, *Scheduling Algorithms*, 4th ed., Springer (2004), Chapter 10 (the MPM flow shop
model);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (shop problems with multipurpose
machines: `FMPM3||C_max`, minimal NP-hard in the strong sense, Garey et al. (1976)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MPMFlowShopThreeMachinesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMFlowShopThreeMachines

/-!
# MULTI-PURPOSE MACHINE FLOW SHOP WITH THREE MACHINES (`FMPM3||C_max`) is NP-complete

INSTANCE: `m = 3` machines `M₁, M₂, M₃`; a number `r` of stages with machine sets
`μ₁, …, μᵣ ⊆ {M₁, M₂, M₃}`, pairwise different; jobs `J₁, …, Jₙ`, each with exactly `r`
operations `Oᵢ₁, …, Oᵢᵣ` with processing times `pᵢⱼ`; and a bound `K`. QUESTION: can every
operation `Oᵢⱼ` be assigned to one machine of `μⱼ` and given a start time so that each machine
processes at most one operation at a time, `Oᵢⱼ` does not start before `Oᵢ,ⱼ₋₁` is completed
(`j = 2, …, r`), and every job completes by `K`?

This is Brucker's MPM flow shop ("For the MPM flow shop problem, each job Jᵢ has exactly r
operations Oᵢⱼ (j = 1, …, r) and there is the same machine set μⱼ associated with the j-th
operation of each job. r is called the number of stages of the problem. Furthermore, all
machine sets are assumed to be different", and an MPM operation is processed on exactly one
machine of its set) with `m = 3` machines and the makespan criterion. Choosing `r = 3` and
`μⱼ = {Mⱼ}` gives the three-machine flow shop `F3||C_max`: its instances `(3, jobs, D)` of
FLOW-SHOP SCHEDULING (`WantedExt.Complexity.NPComplete.FlowShopSchedulingWanted`) map to
`((3, jobs, D), [[0], [1], [2]])`, so NP-hardness follows from Garey, Johnson and Sethi (1976),
who prove `F3||C_max` NP-complete in the strong sense. Membership in NP holds because machine
assignments and start times below `K` are a certificate of polynomial size.

The FLOW-SHOP SCHEDULING instance `(r, jobs, K)` (one list of `r` processing times per job),
its operation lengths `FlowShopScheduling.len` and its well-formedness (`0 < r`, every job has
`r` operations, `0 < K`) are reused; the instance adds the machine sets as lists of machine
indices, machine `Mₖ` being index `k - 1 < m`. A schedule gives each operation (stage `p`, job
`j`) a start time `σ p j` and a machine `a p j`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTI-PURPOSE MACHINE FLOW SHOP WITH THREE MACHINES (`FMPM3||C_max`) is NP-complete.**
Source: Garey, Johnson and Sethi (1976) (`F3||C_max`, the special case `μⱼ = {Mⱼ}`); Brucker
(2004) (model). -/
public theorem_wanted mpmFlowShopThreeMachines_npComplete :
    mpmFlowShopThreeMachinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mpmFlowShopThreeMachinesDec

end MetaMathlibExt.Complexity.NPComplete.MPMFlowShopThreeMachines
