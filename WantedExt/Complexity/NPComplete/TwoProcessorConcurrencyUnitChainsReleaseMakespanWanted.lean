/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UET CONCURRENT TASK SCHEDULING WITH CHAINS AND RELEASE DATES is NP-complete

Source:
P. Brucker, S. Knust, D. Roper and Y. Zinder, "Scheduling UET task systems with concurrency on
two parallel identical processors", Mathematical Methods of Operations Research 52 (2000),
369-387, doi:10.1007/s001860000089 (the full text was not available to us);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 11.5
(`MPT2|chains; rᵢ; pᵢ = 1; sizeᵢ|C_max`, NP-hard in the strong sense, Brucker et al.).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorConcurrencyUnitChainsReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorConcurrencyUnitChainsReleaseMakespan

open ResourceConstrainedScheduling (Task req bound running)
open ResourceConstrainedSchedulingPrecedenceZeroOrBound
  (PrecedenceResourceSchedulingInstance PrecedenceWellFormed Prec)
open ResourceConstrainedSchedulingChainsUnitResource (IsChains)

/-!
# TWO-PROCESSOR UET CONCURRENT TASK SCHEDULING WITH CHAINS AND RELEASE DATES is NP-complete

This is `P2|chains; rᵢ; pᵢ = 1; sizeᵢ|C_max` (Brucker: `MPT2|chains; rᵢ; pᵢ = 1; sizeᵢ|C_max`).

INSTANCE: `m = 2` identical parallel processors, each processing at most one task at a time;
tasks `1, …, n`, each with processing time `pᵢ = 1`, a size `sizeᵢ ∈ {1, 2}` (task `i` needs
`sizeᵢ` processors simultaneously during its processing, any `sizeᵢ` of them) and a release
date `rᵢ ∈ ℤ₀⁺` before which it cannot start; precedence constraints that form a set of chains
(every task has at most one immediate predecessor and at most one immediate successor), where
`i` preceding `j` means that `j` cannot start before `i` is completed; and an integer `K`.
QUESTION: is there a schedule whose makespan `maxᵢ Cᵢ` is at most `K`, `Cᵢ` being the
completion time of task `i`?

Brucker's Table 11.5 lists this problem as NP-hard in the strong sense and credits Brucker,
Knust, Roper and Zinder, whose abstract states that adding precedence constraints to two
processors with tasks that may need both processors makes the maximum lateness problem
NP-hard. Reversing time (start `K - 1 - σ(i)`, reversed chains, due dates `K - rᵢ`) maps this
problem to `P2|chains; pᵢ = 1; sizeᵢ|L_max` with bound `0`.

A task of size `q` occupies `q` of the identical processors, so, as in
`WantedExt.Complexity.NPComplete.ConcurrentTaskSchedulingThreeProcessorsWanted` (Lloyd's
concurrent task systems), the processors act as one resource of bound `m = 2` and the size is
the task's requirement: an instance is a RESOURCE CONSTRAINED SCHEDULING instance with a partial
order (`PrecedenceResourceSchedulingInstance` and `PrecedenceWellFormed` of
`WantedExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBoundWanted`:
unit tasks, a list of the pairs `(i, j)` with `i` preceding `j` that names tasks and forms a
strict partial order, and a positive deadline `D = K`) with `m = 2` processors, `r = 1` resource
of bound `B₁ = 2` and every requirement `R₁(i) = sizeᵢ ∈ {1, 2}`, together with one release date
per task. The order is a set of chains by `IsChains` of
`WantedExt.Complexity.NPComplete.ResourceConstrainedSchedulingChainsUnitResourceWanted`. The
question is `PrecedenceFeasible` of that model (start times `σ(i) ∈ ℤ₀⁺` with `σ(i) + 1 ≤ D`, at
most `m` running tasks, `σ(i) + 1 ≤ σ(j)` when `i` precedes `j`, and running requirements at most
`B₁` at every time) with the release dates `rᵢ ≤ σ(i)` added; the existing predicate quantifies
over its schedule, so its conditions are restated beside the new one. With every requirement at
least `1`, the bound on the number of running tasks follows from the resource bound. Integral
start times lose no generality: rounding every start time down keeps release dates and chains,
and the tasks sharing a rounded start time were all running together just before the next
integer. Well-formedness asks for at least one task (`n ≥ 1`); a nonempty instance needs
`K ≥ 1` for a schedule, so the inherited positive deadline excludes no yes-instance. Binary
encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR UET CONCURRENT TASK SCHEDULING WITH CHAINS AND RELEASE DATES
(`P2|chains; rᵢ; pᵢ = 1; sizeᵢ|C_max`) is NP-complete.** Source: Brucker, Knust, Roper and
Zinder (2000); Brucker (2007), Table 11.5. -/
public theorem_wanted twoProcessorConcurrencyUnitChainsReleaseMakespan_npComplete :
    twoProcessorConcurrencyUnitChainsReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorConcurrencyUnitChainsReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorConcurrencyUnitChainsReleaseMakespan
