/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UNIT-TIME CHAINS SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

Source:
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (the full text was not available to us);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Table 5.3
(`P2|pᵢ = 1; chains|∑wᵢCᵢ`, NP-hard in the strong sense, Timkovsky).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitChainsWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsWeightedCompletion

open TwoProcessorTreePrecedenceCompletionTime
  (TwoProcessorTreePrecedenceCompletionTimeInstance Prec IsInTree IsOutTree
    TwoProcessorTreePrecedenceCompletionTimeFeasible)

/-!
# TWO-PROCESSOR UNIT-TIME CHAINS SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

This is `P2|pᵢ = 1; chains|∑wᵢCᵢ` in the notation of Brucker's *Scheduling Algorithms*.

INSTANCE: `m = 2` identical parallel processors, each processing at most one job at a time; jobs
`1, …, n`, each with processing time `pᵢ = 1` and a weight `wᵢ ∈ ℤ₀⁺`; precedence constraints
that form a set of chains (every job has at most one immediate predecessor and at most one
immediate successor), where `i` preceding `j` means that `j` cannot start before `i` is
completed; and an integer `K`. QUESTION: is there a schedule whose total weighted completion
time `∑ᵢ wᵢCᵢ` is at most `K`, `Cᵢ` being the completion time of job `i`?

Brucker's Table 5.3 lists `P2|pᵢ = 1; chains|∑wᵢCᵢ` as NP-hard in the strong sense and credits
Timkovsky (2003), whose abstract describes polynomial-time reductions between preemptive
problems and unit-time problems with chain-like precedence constraints. Every job is listed
explicitly, so the number of jobs, not only the number of chains, is part of the input size.

The instance, the strict-order precedence relation `Prec`, the chain conditions and the
question are those of the two-processor tree-precedence problem of
`WantedExt.Complexity.NPComplete.TwoProcessorTreePrecedenceCompletionTimeWanted`: one pair
`(pᵢ, wᵢ)` per job, the number of processors, the bound `K`, and the list of the pairs `(i, j)`
with `i` preceding `j`, which must name jobs and form a strict partial order (Mathlib's
`IsStrictOrder`); the question asks for start times in `ℤ₀⁺` such that at every time at most
`m` jobs run, `i` preceding `j` implies `σ(i) + pᵢ ≤ σ(j)`, and `∑ᵢ (σ(i) + pᵢ) · wᵢ ≤ K`. The
order is a set of chains exactly when every job has at most one immediate successor
(`IsInTree`) and at most one immediate predecessor (`IsOutTree`). That problem's
well-formedness asks for equal positive weights and `0 < K`, so it is not reused; here `m = 2`,
every processing time is `1`, weights are arbitrary nonnegative integers, and `K ∈ ℤ₀⁺` (a
negative `K` gives only no-instances). Integral start times lose no generality for unit-time
jobs without release dates, and closing an empty time slot (moving every later job one step
earlier) keeps a schedule feasible without increasing `∑ᵢ wᵢCᵢ`, so start times below `n` form
a certificate of polynomial size. Binary encoding of all numbers (the problem is NP-complete in the
strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR UNIT-TIME CHAINS SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME
(`P2|pᵢ = 1; chains|∑wᵢCᵢ`) is NP-complete.** Source: Timkovsky (2003); Brucker (2007),
Table 5.3. -/
public theorem_wanted twoProcessorUnitChainsWeightedCompletion_npComplete :
    twoProcessorUnitChainsWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitChainsWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitChainsWeightedCompletion
