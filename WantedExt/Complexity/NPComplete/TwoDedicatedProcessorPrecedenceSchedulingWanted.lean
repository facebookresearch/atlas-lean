/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING on 2 dedicated processors is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING, p. 239 (comment: "If each task `t` can only be executed by a specified processor
`p(t)`, the problem is NP-complete for `m = 2` and `<` arbitrary, and for `m` arbitrary and `<` a
forest, but can be solved in polynomial time for `m` arbitrary if `<` is a 'cyclic forest'
[Goyal, 1976]"), citing D. K. Goyal, "Scheduling processor bound systems", Technical Report,
Computer Science Department, Washington State University (1976) (not available to this
formalization).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceScheduling

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task taskLength Prec running)

/-!
# PRECEDENCE CONSTRAINED SCHEDULING on 2 dedicated processors is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, `m = 2` processors, a partial order
`<` on `T`, a deadline `D ∈ ℤ⁺`, and for each task `t ∈ T` a specified processor `p(t)`.
QUESTION: is there an `m`-processor schedule `σ` for `T` that meets the overall deadline `D`,
obeys the precedence constraints, i.e., `t < t'` implies `σ(t') ≥ σ(t) + l(t) = σ(t) + 1`, and
executes each task `t` only on its processor `p(t)`?

This is PRECEDENCE CONSTRAINED SCHEDULING ([SS9], `PrecedenceConstrainedSchedulingWanted`) with
dedicated processors, the variant of the entry's comment, for `m = 2` and `<` arbitrary. The
instance extends the parent's (task lengths, `m`, the pairs `(t, t')` with `t < t'`, `D`) by the
list of the processors `p(t) ∈ {0, …, m - 1}` of the tasks, one per task. The parent's
well-formedness (unit lengths, `m > 0`, the pairs name tasks and form a strict partial order,
`D > 0`), its tasks, lengths, precedence relation and the set `running` of tasks running at a
time are reused. A task executed only on `p(t)` occupies that processor during
`[σ(t), σ(t) + l(t))`, and a processor executes one task at a time, so two different tasks with
the same processor run in disjoint intervals; this implies the parent's bound of `m` tasks
running at a time, which is kept as stated there. `DedicatedWellFormed` and
`DedicatedProcessorsFeasible` state the problem for any `m`; `WellFormed` fixes `m = 2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PRECEDENCE CONSTRAINED SCHEDULING is NP-complete on 2 dedicated processors.** Source: Garey
and Johnson (1979), [SS9], comment (Goyal, 1976). -/
public theorem_wanted twoDedicatedProcessorPrecedenceScheduling_npComplete :
    twoDedicatedProcessorPrecedenceSchedulingDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoDedicatedProcessorPrecedenceSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceScheduling
