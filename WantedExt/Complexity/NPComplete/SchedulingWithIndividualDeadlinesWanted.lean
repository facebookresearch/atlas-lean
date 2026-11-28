/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING WITH INDIVIDUAL DEADLINES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS11] SCHEDULING WITH INDIVIDUAL
DEADLINES;
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlinesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlines

/-!
# SCHEDULING WITH INDIVIDUAL DEADLINES is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, a number `m ∈ ℤ⁺` of processors, a
partial order `<` on `T`, and for each task `t ∈ T` a deadline `d(t) ∈ ℤ⁺`. QUESTION: is there an
`m`-processor schedule `σ` for `T` that obeys the precedence constraints and meets all the
deadlines, i.e., `σ(t) + l(t) ≤ d(t)` for all `t ∈ T`?

An `m`-processor schedule is a start time `σ(t) ∈ ℤ₀⁺` for each task such that at every time `u`
at most `m` tasks run (`σ(t) ≤ u < σ(t) + l(t)`); it obeys the precedence constraints when
`t < t'` implies `σ(t') ≥ σ(t) + l(t)`. Tasks are `Fin n`, one per deadline. The partial order is
given by the list of its pairs `(t, t')` with `t < t'`, required to be a strict order (Mathlib's
`IsStrictOrder`: irreflexive and transitive). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SCHEDULING WITH INDIVIDUAL DEADLINES is NP-complete.** Source: Garey and Johnson
(1979), [SS11]; Brucker, Garey and Johnson (1977). -/
public theorem_wanted schedulingWithIndividualDeadlines_npComplete :
    schedulingWithIndividualDeadlinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L schedulingWithIndividualDeadlinesDec

end MetaMathlibExt.Complexity.NPComplete.SchedulingWithIndividualDeadlines
