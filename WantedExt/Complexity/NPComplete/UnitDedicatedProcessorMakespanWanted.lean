/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT-TIME DEDICATED-PROCESSOR SCHEDULING, MAKESPAN (P|fixⱼ, pⱼ = 1|C_max) is NP-complete

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.5 (deciding whether an instance of
`P|fixⱼ, pⱼ = 1|C_max` has a schedule of length at most 3 is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Multiprocessor task problems with
dedicated processors", which lists the problem as minimal NP-hard with this attribution.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespan

/-!
# UNIT-TIME DEDICATED-PROCESSOR SCHEDULING, MAKESPAN (P|fixⱼ, pⱼ = 1|C_max) is NP-complete

INSTANCE: `m` processors (`m` part of the input), each processing at most one task at a time,
and tasks `1, …, n`, each with processing time `pⱼ = 1` and a prespecified set `fixⱼ` of
processors, all of which it requires simultaneously during its processing (so two tasks whose
sets intersect cannot overlap in time); a positive integer `K`. QUESTION: is there a feasible
schedule with makespan `max_j Cⱼ ≤ K`, where `Cⱼ` is the completion time of task `j`?

The processors are `0, …, m - 1` and each set `fixⱼ` is a nonempty list of processors without
repetitions. A schedule gives each task a start time `s j ∈ ℕ` and the completion time
`Cⱼ = s j + 1`; two different tasks with a common processor are processed in disjoint time
intervals, as in `ThreeDedicatedProcessorSchedulingWanted` (the problem with three processors
and arbitrary lengths). Integral start times lose no generality for unit-time tasks without
release dates. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNIT-TIME DEDICATED-PROCESSOR SCHEDULING with makespan bound (`P|fixⱼ, pⱼ = 1|C_max`) is
NP-complete.** Source: Hoogeveen, van de Velde and Veltman (1994), Theorem 2.5. -/
public theorem_wanted unitDedicatedProcessorMakespan_npComplete :
    unitDedicatedProcessorMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitDedicatedProcessorMakespanDec

end MetaMathlibExt.Complexity.NPComplete.UnitDedicatedProcessorMakespan
