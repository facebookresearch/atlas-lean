/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE TARDY TASKS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS2] SEQUENCING TO MINIMIZE
TARDY TASKS, and Section 3.2.3, Theorem 3.10, p. 73 (MINIMUM TARDINESS SEQUENCING,
transformation from CLIQUE);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeTardyTasksDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeTardyTasks

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SEQUENCING TO MINIMIZE TARDY TASKS is NP-complete

INSTANCE: a set `T` of tasks, a partial order `<` on `T`, for each task `t ∈ T` a length
`l(t) ∈ ℤ⁺` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K ≤ |T|`.
QUESTION: is there a one-processor schedule `σ` for `T` that obeys the precedence constraints,
i.e. such that `t < t'` implies `σ(t) + l(t) ≤ σ(t')`, and such that there are at most `K` tasks
`t ∈ T` for which `σ(t) + l(t) > d(t)`?

Garey and Johnson prove this NP-complete (Section 3.2.3, Theorem 3.10) already for unit lengths
(MINIMUM TARDINESS SEQUENCING, a transformation from CLIQUE), and Lenstra and Rinnooy Kan (Theorem
1) for unit lengths with precedence constraints that consist of chains
(`TardyTasksUnitChainsWanted`, the restriction of this problem stated with the same definitions).
Membership in NP: the schedule is a certificate; its start times can be taken below the total
length, so they have polynomially many bits. Binary encoding of all numbers.

The tasks are `Fin n`, one per listed pair `(l(t), d(t))`. A one-processor schedule is Garey and
Johnson's [SS1] notion, reused from `SequencingToMinimizeWeightedTardinessDefs`
(`IsOneProcessorSchedule`, a one-to-one `σ : T → ℤ₀⁺` with `σ(t) > σ(t')` implying
`σ(t) ≥ σ(t') + l(t')`). The partial order is given by the list of its pairs `(t, t')` with
`t < t'`, required to be a strict order (Mathlib's `IsStrictOrder`), as in
`TardyTasksUnitChainsWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SEQUENCING TO MINIMIZE TARDY TASKS is NP-complete.** Source: Garey and Johnson
(1979), [SS2] and Section 3.2.3; Lenstra and Rinnooy Kan (1980), Theorem 1. -/
public theorem_wanted sequencingToMinimizeTardyTasks_npComplete :
    sequencingToMinimizeTardyTasksDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingToMinimizeTardyTasksDec

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeTardyTasks
