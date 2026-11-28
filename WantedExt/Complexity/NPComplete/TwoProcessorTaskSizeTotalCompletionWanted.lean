/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR TASKS, TOTAL COMPLETION TIME `P2|size_i|ΣC_i` is NP-complete

Source:
C.-Y. Lee and X. Cai, "Scheduling one and two-processor tasks on two parallel processors",
IIE Transactions 31 (1999), 445-455, doi:10.1080/07408179908969847 (only the abstract was
available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on
parallel processors, without preemption), entry `P2|size_i|ΣC_i` (minimal NP-hard, citing Lee
and Cai 1999);
K. Jansen and K. Kahler, "On the complexity of scheduling problems with a fixed number of
parallel identical machines", Lecture Notes in Computer Science, Springer, 192-206,
doi:10.1007/978-3-031-23101-8_13 (records that Lee and Cai proved `P2|size|ΣC_j` NP-hard and
that its strong NP-hardness is open).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorTaskSizeTotalCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeTotalCompletion

/-!
# TWO-PROCESSOR TASKS, TOTAL COMPLETION TIME `P2|size_i|ΣC_i` is NP-complete

INSTANCE: two identical processors, each executing at most one task at a time; `n` tasks, task
`i` with a processing time `p_i ∈ ℤ₀⁺` and a size `size_i ∈ {1, 2}` (the task uses `size_i`
processors, any of them, simultaneously during its whole uninterrupted processing); and a bound
`K`. QUESTION: is there a schedule with total completion time `∑_i C_i ≤ K`, where `C_i` is the
completion time of task `i`?

Lee and Cai study two processors where some tasks are processed by one processor and the others
by both processors simultaneously. They prove the total weighted completion time problem
NP-hard in the strong sense and the unweighted problem `P2|size_i|ΣC_i` NP-hard; Jansen and
Kahler record both results and that strong NP-hardness of the unweighted problem is open. The
Brucker-Knust tables record `P2|size_i|ΣC_i` as minimal NP-hard, credited to Lee and Cai.

Tasks are listed one per entry as `(p_i, size_i)`; tasks are `Fin n`. A schedule is given by
start times, so `C_i = s_i + p_i`; processors are not named: start times admit an assignment of
processors, each task keeping its processors throughout its processing, exactly when at every
time the sizes of the running tasks sum to at most `2` (replacing each task by `size_i` copies
of its interval gives an interval graph, whose chromatic number is its largest clique). Start
times are natural numbers: rounding all start times down keeps the capacity (two tasks that do
not overlap still do not, and pairwise overlapping intervals share a point) and does not
increase the total completion time. Membership in NP is the certificate argument: in a
yes-instance every start time is at most `K`, and the `n` start times are checked in polynomial
time (the running set changes only at the `2n` start and completion times). Numbers use the
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR TASKS, TOTAL COMPLETION TIME `P2|size_i|ΣC_i` is NP-complete.** Source: Lee
and Cai (1999), as recorded in the Brucker-Knust classification. -/
public theorem_wanted twoProcessorTaskSizeTotalCompletion_npComplete :
    twoProcessorTaskSizeTotalCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorTaskSizeTotalCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeTotalCompletion
