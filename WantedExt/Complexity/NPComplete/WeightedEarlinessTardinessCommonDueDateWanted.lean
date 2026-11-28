/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE is NP-complete

Source:
N. G. Hall and M. E. Posner, "Earliness-tardiness scheduling problems, I: weighted deviation of
completion times about a common due date", Operations Research 39 (1991), 836-846,
doi:10.1287/opre.39.5.836.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeightedEarlinessTardinessCommonDueDateDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedEarlinessTardinessCommonDueDate

/-!
# WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE is NP-complete

INSTANCE: a single machine; jobs `1, …, n` with processing times `p_j ∈ ℤ⁺` and weights
`w_j ∈ ℤ₀⁺`; a common due date `d` with `d ≥ ∑_j p_j` (the due date is unrestrictive: it is not
early enough to constrain the schedule); and a bound `K`.
QUESTION: is there a nonpreemptive schedule of the jobs on the machine whose total weighted
deviation `∑_j w_j |C_j - d|` of the completion times `C_j` from `d` is at most `K`?

In the three-field notation this is `1|d_j = d|∑ w_j |C_j - d|` with `d ≥ ∑_j p_j`. Hall and
Posner prove that its recognition version is NP-complete in the ordinary sense, and give a
pseudopolynomial dynamic program, so the binary encoding of the numbers matters. A schedule
assigns each job a start time `S_j ∈ ℤ₀⁺` (time starts at `0`; idle time is allowed); the
machine processes one job at a time, so the intervals `[S_j, S_j + p_j)` of distinct jobs are
disjoint, and `C_j = S_j + p_j`. The weighted deviation is written with `Int.natAbs`. The bound
`K` is a natural number (the objective is nonnegative).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEIGHTED EARLINESS-TARDINESS ABOUT A COMMON DUE DATE is NP-complete.** Source: Hall and
Posner (1991). -/
public theorem_wanted weightedEarlinessTardinessCommonDueDate_npComplete :
    weightedEarlinessTardinessCommonDueDateDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedEarlinessTardinessCommonDueDateDec

end MetaMathlibExt.Complexity.NPComplete.WeightedEarlinessTardinessCommonDueDate
