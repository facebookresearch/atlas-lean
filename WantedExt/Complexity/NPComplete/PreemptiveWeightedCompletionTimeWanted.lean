/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME, comment on p. 240 ("These results continue to hold if "preemptive"
schedules are allowed [McNaughton, 1959]"), with preemptive schedules as in [SS12];
R. McNaughton, "Scheduling with deadlines and loss functions", Management Science 6 (1959),
1-12, doi:10.1287/mnsc.6.1.1;
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTime

open MetaMathlibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTime
  (SchedulingToMinimizeWeightedCompletionTimeInstance Task taskLength weight)

/-!
# PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

INSTANCE: a set `T` of tasks, a number `m ∈ ℤ⁺` of processors, for each task `t ∈ T` a length
`l(t) ∈ ℤ⁺` and a weight `w(t) ∈ ℤ⁺`, and a positive integer `K`.
QUESTION: is there an `m`-processor "preemptive" schedule for `T` such that the sum, over all
`t ∈ T`, of the completion time of `t` times `w(t)` is no more than `K`?

The instance and its well-formedness (`m > 0`, positive lengths and weights, `K > 0`) are those
of SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME
(`WantedExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeWanted`); the
question allows preemption. Following Garey and Johnson's definition in [SS12], a preemptive
schedule subdivides each task `t` into subtasks `t₁, …, t_k` with `∑ l(tᵢ) = l(t)`, requires
`σ(tᵢ₊₁) ≥ σ(tᵢ) + l(tᵢ)`, and is an ordinary `m`-processor schedule [SS8] of the subtasks: for
all `u ≥ 0`, at most `m` subtasks `s` have `σ(s) ≤ u < σ(s) + l(s)`. Here the subtasks of `t`
are a list of pieces `(σ(tᵢ), l(tᵢ))` with positive lengths, and the completion time of `t` is
the end `σ(t_k) + l(t_k)` of its last piece; with one piece per task this is the parent's
`(σ(t) + l(t)) · w(t)` objective.

Garey and Johnson state that the results for the parent problem (NP-complete for `m = 2`, in
the strong sense for `m` arbitrary) continue to hold with preemption, citing McNaughton (1959):
on identical processors preemption does not decrease the weighted sum of completion times, so a
preemptive schedule meeting `K` exists exactly when a nonpreemptive one does. The parent's
NP-completeness is due to Lenstra, Rinnooy Kan and Brucker (1977). Membership in NP follows
from the same equivalence: the certificate is a nonpreemptive schedule (one piece per task),
with start times at most `K`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete.** Source: Garey
and Johnson (1979), [SS13]; McNaughton (1959); Lenstra, Rinnooy Kan and Brucker (1977). -/
public theorem_wanted preemptiveWeightedCompletionTime_npComplete :
    preemptiveWeightedCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L preemptiveWeightedCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTime
