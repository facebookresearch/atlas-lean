/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DEDICATED PROCESSOR SCHEDULING is NP-complete

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.3;
J. Błażewicz, P. Dell'Olmo, M. Drozdowski and M. G. Speranza, "Scheduling multiprocessor tasks on
three dedicated processors", Information Processing Letters 41 (1992), 275-280,
doi:10.1016/0020-0190(92)90172-R;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry
MINIMUM 3-DEDICATED PROCESSOR SCHEDULING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreeDedicatedProcessorSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDedicatedProcessorScheduling

/-!
# 3-DEDICATED PROCESSOR SCHEDULING is NP-complete

INSTANCE: a set `T` of tasks, a set `P` of `3` processors, for each task `t ∈ T` a length
`l(t) ∈ ℤ⁺` and a required subset of processors `r(t) ⊆ P`, and a positive integer `K`.
QUESTION: is there a schedule, a start time `s(t)` for each task, such that any two tasks `t₁`,
`t₂` with `r(t₁) ∩ r(t₂) ≠ ∅` are not processed at the same time, with makespan
`max_{t ∈ T} (s(t) + l(t)) ≤ K`?

Each task occupies every processor of `r(t)` during `[s(t), s(t) + l(t))`, and each processor
executes at most one task at a time (Hoogeveen, van de Velde and Veltman, Section 1: "an
allocation of each task `J_j` to a time interval of length `p_j` such that no two tasks on the
same processor overlap"). This is the decision version of `P3|fix_j|C_max`, which Hoogeveen, van
de Velde and Veltman prove NP-hard in the strong sense (Theorem 2.3, by a reduction from
3-PARTITION), crediting the first proof to Błażewicz, Dell'Olmo, Drozdowski and Speranza.

Encoding: processors are `0, 1, 2`; the tasks are listed as pairs `(l(t), r(t))`, the processor
set as a list without repetitions, and the tasks are `Fin n` for `n` listed tasks. Start times
are natural numbers (with integer data, integer start times lose no generality). Two tasks that
share a processor occupy disjoint intervals: one finishes no later than the other starts.
Well-formedness: positive lengths, nonempty processor sets of processors below `3`, and `0 < K`.
Binary encoding of all numbers (the problem is NP-complete in the strong sense).
The instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3-DEDICATED PROCESSOR SCHEDULING is NP-complete.** Source: Hoogeveen, van de Velde and
Veltman (1994), Theorem 2.3; Błażewicz, Dell'Olmo, Drozdowski and Speranza (1992). -/
public theorem_wanted threeDedicatedProcessorScheduling_npComplete :
    threeDedicatedProcessorSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeDedicatedProcessorSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.ThreeDedicatedProcessorScheduling
