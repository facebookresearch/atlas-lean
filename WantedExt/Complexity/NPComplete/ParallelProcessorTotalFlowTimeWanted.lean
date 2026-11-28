/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL PROCESSOR TOTAL FLOW TIME is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM PARALLEL PROCESSOR TOTAL FLOW TIME (decision version);
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (the case `m = 1`, `1|rⱼ|∑ Cⱼ`, is strongly NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ParallelProcessorTotalFlowTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelProcessorTotalFlowTime

open TotalCompletionTimeWithReleaseTimes (TotalCompletionTimeWithReleaseTimesInstance Task
  taskLength releaseTime)

/-!
# PARALLEL PROCESSOR TOTAL FLOW TIME is NP-complete

INSTANCE: a set `T` of tasks, a number `m` of identical processors, for each task `t ∈ T` a
release time `r(t) ∈ ℤ⁺` and a length `l(t) ∈ ℤ⁺`, and a positive integer `K`.
QUESTION: is there an `m`-processor schedule for `T` that obeys the resource constraints and
the release times, that is, a function `f : T → ℕ × [1..m]` (start time and processor) such
that each processor runs at most one task at a time and every task starts no earlier than its
release time, with total flow time `∑_{t ∈ T} (f(t)₁ + l(t) - r(t)) ≤ K`?

The tasks are listed as pairs `(l(t), r(t))`; the task type, lengths and release times are
reused from `TotalCompletionTimeWithReleaseTimesWanted` (the case `m = 1` with total completion
time `∑ (σ(t) + l(t))`). A schedule is a start time `σ(t)` and a processor `p(t) ∈ Fin m` for
each task, where two different tasks on the same processor do not overlap. The flow time of a
task is its completion time minus its release time, `σ(t) + l(t) - r(t)` (natural-number
subtraction is exact here because `r(t) ≤ σ(t)`). Crescenzi and Kann print the measure as
`∑ (f(t)₁ - r(t))` with the start time `f(t)₁`, which differs from the total flow time by the
constant `∑ l(t)`, and write the resource constraint as `|S(u, i)| = 1` for the set `S(u, i)`
of tasks running on processor `i` at time `u`; it is read as "at most one task", since
otherwise idle processors would be forbidden. For `m = 1` the question is
`1|rⱼ|∑ Cⱼ ≤ K + ∑ r(t)`, which gives NP-hardness. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARALLEL PROCESSOR TOTAL FLOW TIME is NP-complete.** Source: Crescenzi and Kann, MINIMUM
PARALLEL PROCESSOR TOTAL FLOW TIME; Lenstra, Rinnooy Kan and Brucker (1977) for `m = 1`. -/
public theorem_wanted parallelProcessorTotalFlowTime_npComplete :
    parallelProcessorTotalFlowTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L parallelProcessorTotalFlowTimeDec

end MetaMathlibExt.Complexity.NPComplete.ParallelProcessorTotalFlowTime
