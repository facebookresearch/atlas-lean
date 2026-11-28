/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIT-TIME PARALLEL-TASK SCHEDULING, TOTAL COMPLETION TIME (P|sizeⱼ, pⱼ = 1|∑ Cⱼ) is NP-complete

Source:
M. Drozdowski and P. Dell'Olmo, "Scheduling multiprocessor tasks for mean flow time criterion",
Computers & Operations Research 27 (2000), 571-585, doi:10.1016/S0305-0548(99)00048-9 (abstract:
"When tasks have unit execution time and the number of processors is arbitrary the problem is
shown to be computationally hard");
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Multiprocessor task problems with
parallel processors", which lists `P|pᵢ = 1; sizeᵢ|∑ Cᵢ` as minimal NP-hard with this
attribution.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnitParallelTaskCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitParallelTaskCompletionTime

/-!
# UNIT-TIME PARALLEL-TASK SCHEDULING, TOTAL COMPLETION TIME (P|sizeⱼ, pⱼ = 1|∑ Cⱼ) is NP-complete

INSTANCE: `m` identical processors (`m` part of the input), each processing at most one task at
a time, and tasks `1, …, n`, each with processing time `pⱼ = 1` and requiring `sizeⱼ` processors
simultaneously during its processing (an integer `1 ≤ sizeⱼ ≤ m`; any `sizeⱼ` processors may be
used); a positive integer `K`. QUESTION: is there a feasible schedule with total completion time
`∑ⱼ Cⱼ ≤ K`, where `Cⱼ` is the completion time of task `j`? (Without release dates the total
completion time is the total flow time, `n` times the mean flow time of the source.)

A schedule gives each task a start time `s j ∈ ℕ`, so `Cⱼ = s j + 1`. A unit-time task started at
`s j` is processed exactly during `[s j, s j + 1)`, so the tasks processed at time `t` are those
with `s j = t`, and they fit on the `m` processors exactly when their sizes sum to at most `m`.
Integral start times lose no generality for unit-time tasks without release dates. Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNIT-TIME PARALLEL-TASK SCHEDULING with total completion time bound
(`P|sizeⱼ, pⱼ = 1|∑ Cⱼ`) is NP-complete.** Source: Drozdowski and Dell'Olmo (2000). -/
public theorem_wanted unitParallelTaskCompletionTime_npComplete :
    unitParallelTaskCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitParallelTaskCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.UnitParallelTaskCompletionTime
