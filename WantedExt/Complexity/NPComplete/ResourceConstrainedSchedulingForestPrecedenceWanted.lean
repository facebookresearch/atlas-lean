/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with forest precedence is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED
SCHEDULING, p. 239, comment: "If a partial order < is added, the problem becomes NP-complete in
the strong sense for r = 1, m = 2, and < a "forest."", within the entry whose reference is
[Garey and Johnson, 1975];
M. R. Garey and D. S. Johnson, "Complexity results for multiprocessor scheduling under resource
constraints", SIAM Journal on Computing 4 (1975), 397-411, doi:10.1137/0204035.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingForestPrecedenceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingForestPrecedence

open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling (Task)
open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBound
  (PrecedenceResourceSchedulingInstance Prec PrecedenceWellFormed PrecedenceFeasible)

/-!
# RESOURCE CONSTRAINED SCHEDULING with forest precedence is NP-complete

The problem RESOURCE CONSTRAINED SCHEDULING
(`MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling`) with a partial order `<`
on the tasks added, in the case `r = 1`, `m = 2` and `<` a forest. INSTANCE: a set `T` of tasks,
each having length `l(t) = 1`, `m = 2` processors, `r = 1` resource with bound `B_1 ∈ ℤ⁺`, a
resource requirement `R_1(t)` with `0 ≤ R_1(t) ≤ B_1` for each task `t`, a partial order `<` on
`T` that is a forest, and an overall deadline `D ∈ ℤ⁺`. QUESTION: is there an `m`-processor
schedule `σ` for `T` that meets the overall deadline `D`, obeys the precedence constraints
(`t < t'` implies `σ(t') ≥ σ(t) + 1`) and obeys the resource constraints, i.e., such that for all
`u ≥ 0`, if `S(u)` is the set of all `t ∈ T` for which `σ(t) ≤ u < σ(t) + l(t)`, then for each
resource `i` the sum of `R_i(t)` over all `t ∈ S(u)` is at most `B_i`?

The instance encoding, the precedence relation, the well-formedness of the problem with a partial
order and the question are those of
`MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBound`
(`PrecedenceWellFormed`, `PrecedenceFeasible`); here additionally `m = 2`, `r = 1` and `<` is a
forest. Following Garey and Johnson (Figure 4.1 and [SS11], comment), `t` is an immediate
predecessor of `t'` (and `t'` an immediate successor of `t`) when `t < t'` and no task `c` has
`t < c < t'`; an in-tree order is one in which each task has at most one immediate successor, and
an out-tree order one in which each task has at most one immediate predecessor. Garey and Johnson
do not define "forest"; it is read here as an in-forest or an out-forest. Reversing time
(`σ'(t) = D - 1 - σ(t)`) maps the schedules of an instance to those of the instance with the
reversed order, keeping the processor and resource constraints, and reverses an in-forest into an
out-forest, so both readings give the same problem up to this reduction. Numbers use the binary
encoding (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RESOURCE CONSTRAINED SCHEDULING with `r = 1`, `m = 2` and a forest partial order is
NP-complete.** Source: Garey and Johnson (1979), [SS10], comment; Garey and Johnson (1975). -/
public theorem_wanted resourceConstrainedSchedulingForestPrecedence_npComplete :
    resourceConstrainedSchedulingForestPrecedenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L resourceConstrainedSchedulingForestPrecedenceDec

end MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingForestPrecedence
