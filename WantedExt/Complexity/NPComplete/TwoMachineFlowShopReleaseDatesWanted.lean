/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE FLOW SHOP WITH RELEASE DATES (F2|r_j|C_max) is NP-complete

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X;
recorded in E. L. Lawler, J. K. Lenstra, A. H. G. Rinnooy Kan and D. B. Shmoys, "Sequencing and
scheduling: algorithms and complexity" (1989/1993), and in P. Brucker and S. Knust, "Complexity
results for scheduling problems" (minimal NP-hard `F2|r_i|C_max`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoMachineFlowShopReleaseDatesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineFlowShopReleaseDates

/-!
# TWO-MACHINE FLOW SHOP WITH RELEASE DATES (F2|r_j|C_max) is NP-complete

INSTANCE: two machines `M₁, M₂` in a flow shop and jobs `j`, each consisting of an operation of
length `p₁ⱼ ∈ ℤ₀⁺` on `M₁` followed by an operation of length `p₂ⱼ ∈ ℤ₀⁺` on `M₂` (the second
cannot start before the first is completed); each machine processes at most one operation at a
time; job `j` has a release date `rⱼ ∈ ℤ₀⁺` and cannot start before it; and a bound `K`.
QUESTION: is there a feasible schedule with makespan `max_j Cⱼ ≤ K`, where `Cⱼ` is the
completion time of job `j`?

This is FLOW-SHOP SCHEDULING ([SS15], `FlowShopScheduling`) with `m = 2` processors, the
deadline `D` read as the makespan bound `K` (every operation ends by `D` iff the makespan is at
most `D`), and release dates added. The instance pairs the parent's instance with the list of
release dates; `WellFormed` asks for `m = 2`, two tasks per job and one release date per job (all
data, `K` included, may be `0`, as in the scheduling model; the parent's `D ∈ ℤ⁺` is not
imposed). The schedule conditions are the parent's (every task ends
by `D`, one task at a time on each processor, each job's tasks in processor order) plus
`rⱼ ≤ σ(M₁, j)`; with the flow-shop order this is "job `j` cannot start before `rⱼ`".
Processors are `Fin m`, jobs `Fin |J|`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-MACHINE FLOW SHOP WITH RELEASE DATES (F2|r_j|C_max) is NP-complete.**
Source: Lenstra, Rinnooy Kan and Brucker (1977). -/
public theorem_wanted twoMachineFlowShopReleaseDates_npComplete :
    twoMachineFlowShopReleaseDatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineFlowShopReleaseDatesDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineFlowShopReleaseDates
