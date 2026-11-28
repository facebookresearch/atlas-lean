/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR TASKS WITH RELEASE DATES `P2|r_i;size_i|Cmax` is NP-complete

Source:
C.-Y. Lee and X. Cai, "Scheduling one and two-processor tasks on two parallel processors",
IIE Transactions 31 (1999), 445-455, doi:10.1080/07408179908969847 (only the abstract was
available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on
parallel processors, without preemption), entry `P2|r_i;size_i|C_max` (minimal NP-hard in the
strong sense, citing Lee and Cai 1999).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorTaskSizeReleaseDatesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeReleaseDates

/-!
# TWO-PROCESSOR TASKS WITH RELEASE DATES `P2|r_i;size_i|Cmax` is NP-complete

INSTANCE: two identical processors, each executing at most one task at a time; `n` tasks, task
`i` with a processing time `p_i ∈ ℤ₀⁺`, a size `size_i ∈ {1, 2}` (the task uses `size_i`
processors, any of them, simultaneously during its whole uninterrupted processing), and a release
date `r_i ∈ ℤ₀⁺` before which it cannot start; and a bound `K`. QUESTION: is there a schedule
with makespan `max_i C_i ≤ K`, where `C_i` is the completion time of task `i`?

Lee and Cai's abstract states that minimizing the maximum lateness with one- and two-processor
tasks on two processors (`P2|size_i|L_max`) is strongly NP-complete (their appendix). Reversing
time turns the deadlines `d_i + L` of a maximum-lateness bound `L` into release dates and the
latest deadline into a makespan bound, which gives this problem; the Brucker-Knust tables record
`P2|r_i;size_i|C_max` as strongly NP-hard, credited to Lee and Cai.

Tasks are listed one per entry as `(p_i, size_i, r_i)`; tasks are `Fin n`. A schedule is given by
start times; processors are not named: start times admit an assignment of processors, each task
keeping its processors throughout its processing, exactly when at every time the sizes of the
running tasks sum to at most `2` (replacing each task by `size_i` copies of its interval gives an
interval graph, whose chromatic number is its largest clique). Start times are natural numbers:
rounding all start times down keeps the release dates and the capacity (two tasks that do not
overlap still do not, and pairwise overlapping intervals share a point) and does not increase the
makespan. Membership in NP is the certificate argument: the `n` start times, each at most `K`,
are checked in polynomial time (the running set changes only at the `2n` start and completion
times). Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO-PROCESSOR TASKS WITH RELEASE DATES `P2|r_i;size_i|Cmax` is NP-complete.** Source:
Lee and Cai (1999), as recorded in the Brucker-Knust classification. -/
public theorem_wanted twoProcessorTaskSizeReleaseDates_npComplete :
    twoProcessorTaskSizeReleaseDatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorTaskSizeReleaseDatesDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeReleaseDates
