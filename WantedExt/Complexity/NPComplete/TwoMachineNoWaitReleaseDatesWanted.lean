/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE NO-WAIT FLOW SHOP WITH RELEASE DATES (F2|r_j;no-wait|C_max) is NP-complete

Source:
H. Röck, "Some new results in flow shop scheduling", Zeitschrift für Operations Research 28
(1984), 1-16, doi:10.1007/BF01919082; recorded in P. Brucker and S. Knust, "Complexity results
for scheduling problems" (minimal NP-hard `F2|r_i;no-wait|C_max`, Röck 1984) and in E. L. Lawler,
J. K. Lenstra, A. H. G. Rinnooy Kan and D. B. Shmoys, "Sequencing and scheduling: algorithms and
complexity" (1989/1993) (`F2|no wait|L_max` strongly NP-hard, Röck 1984).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoMachineNoWaitReleaseDatesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineNoWaitReleaseDates

/-!
# TWO-MACHINE NO-WAIT FLOW SHOP WITH RELEASE DATES (F2|r_j;no-wait|C_max) is NP-complete

INSTANCE: two machines `M₁, M₂` in a flow shop and jobs `j`, each consisting of an operation of
length `p₁ⱼ ∈ ℤ₀⁺` on `M₁` followed by an operation of length `p₂ⱼ ∈ ℤ₀⁺` on `M₂`; each machine
processes at most one operation at a time; job `j` has a release date `rⱼ ∈ ℤ₀⁺` and cannot start
before it; no-wait: each operation of a job starts exactly when the preceding operation of the
same job is completed; and a bound `K`.
QUESTION: is there a feasible schedule with makespan `max_j Cⱼ ≤ K`?

This is FLOW-SHOP SCHEDULING ([SS15], `FlowShopScheduling`) with `m = 2` processors, the
deadline `D` read as the makespan bound `K`, release dates added, and the no-wait condition of
NO-WAIT FLOW-SHOP SCHEDULING ([SS16]) `σᵢ₊₁(j) = σᵢ(j) + l(tᵢ[j])`. The schedule conditions are
those of `FlowShopScheduling` (one task at a time on each processor as non-overlap, as in
the scheduling model of the source) rather than those of `NoWaitFlowShopSchedulingWanted`, whose
one-processor schedules are also one-to-one, a condition the `α|β|γ` model does not impose on
zero-length operations. The instance pairs the parent's instance with the list of release dates;
`WellFormed` asks for `m = 2`, two tasks per job and one release date per job (all data, `K`
included, may be `0`; the parent's `D ∈ ℤ⁺` is not imposed). Processors are `Fin m`, jobs
`Fin |J|`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-MACHINE NO-WAIT FLOW SHOP WITH RELEASE DATES (F2|r_j;no-wait|C_max) is NP-complete.**
Source: Röck (1984). -/
public theorem_wanted twoMachineNoWaitReleaseDates_npComplete :
    twoMachineNoWaitReleaseDatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineNoWaitReleaseDatesDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineNoWaitReleaseDates
