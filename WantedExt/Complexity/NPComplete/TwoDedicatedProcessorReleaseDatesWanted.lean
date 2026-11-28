/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO DEDICATED PROCESSORS WITH RELEASE DATES `P2|r_i;fix_i|Cmax` is NP-complete

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `mpt` (multiprocessor tasks), entry
`P2|r_i;fix_i|C_max` (minimal NP-hard in the strong sense, citing Hoogeveen et al. 1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoDedicatedProcessorReleaseDatesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorReleaseDates

/-!
# TWO DEDICATED PROCESSORS WITH RELEASE DATES `P2|r_i;fix_i|Cmax` is NP-complete

INSTANCE: two processors `M₁`, `M₂`, each executing at most one task at a time; `n` tasks, task
`i` with a processing time `p_i ∈ ℤ⁺`, a nonempty set `fix_i ⊆ {M₁, M₂}` of processors that it
uses simultaneously during its whole (uninterrupted) processing, and a release date
`r_i ∈ ℤ₀⁺` before which it cannot start; and a bound `K`. Tasks whose processor sets intersect
cannot overlap in time. QUESTION: is there a schedule with makespan `max_i C_i ≤ K`, where `C_i`
is the completion time of task `i`?

Hoogeveen, van de Velde and Veltman (Section 1) define a schedule as "an allocation of each task
`J_j` to a time interval of length `p_j` such that no two tasks on the same processor overlap",
with the release date `r_j` "on which it becomes available for processing"; Theorem 2.8 proves
`P2|fix_j, r_j|C_max` NP-hard in the strong sense by a reduction from 3-PARTITION.

Tasks are listed one per entry as `(p_i, fix_i, r_i)`, the processor set as a list without
repetitions of processors `0, 1` (for `M₁, M₂`); tasks are `Fin n`. Start times are natural
numbers: once the order of the tasks on each processor is fixed, every constraint is a
difference constraint with integer constants, which has an integer solution whenever it has a
real one. Membership in NP is the certificate argument: the `n` start times, each at most `K`,
are checked in polynomial time. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TWO DEDICATED PROCESSORS WITH RELEASE DATES `P2|r_i;fix_i|Cmax` is NP-complete.** Source:
Hoogeveen, van de Velde and Veltman (1994), Theorem 2.8; Brucker and Knust (classification
tables). -/
public theorem_wanted twoDedicatedProcessorReleaseDates_npComplete :
    twoDedicatedProcessorReleaseDatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoDedicatedProcessorReleaseDatesDec

end MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorReleaseDates
