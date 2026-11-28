/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING WITH DEADLINES AND CHANGEOVER COSTS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS6] SEQUENCING WITH DEADLINES AND
SET-UP TIMES, p. 238 (comment: "The related problem in which set-up times are replaced by
'changeover costs,' and we want to know if there is a schedule that meets all the deadlines and
has total changeover cost at most `K`, is NP-complete even if all changeover costs are equal");
J. Bruno and P. Downey, "Complexity of task sequencing with deadlines, set-up times and
changeover costs", SIAM Journal on Computing 7 (1978), 393-404, doi:10.1137/0207031.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SequencingWithDeadlinesAndChangeoverCostsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndChangeoverCosts

open MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndSetUpTimes
  (SequencingWithDeadlinesAndSetUpTimesInstance Task taskLength deadline compiler
    IsOneProcessorSchedule)

/-!
# SEQUENCING WITH DEADLINES AND CHANGEOVER COSTS is NP-complete

INSTANCE: a set `C` of "compilers", a set `T` of tasks, for each `t ∈ T` a length
`l(t) ∈ ℤ⁺`, a deadline `d(t) ∈ ℤ⁺` and a compiler `k(t) ∈ C`, for each `c ∈ C` a "changeover
cost" `γ(c) ∈ ℤ₀⁺`, and a bound `K ∈ ℤ₀⁺`.
QUESTION: is there a one-processor schedule `σ` for `T` that meets all the task deadlines and
whose total changeover cost is at most `K`, where a changeover cost `γ(k(t'))` is incurred
whenever two tasks `t` and `t'` with `σ(t) < σ(t')` are scheduled "consecutively" (no other task
`t''` has `σ(t) < σ(t'') < σ(t')`) and have different compilers (`k(t) ≠ k(t')`)?

This is the related problem in the comment of [SS6] SEQUENCING WITH DEADLINES AND SET-UP TIMES
(`SequencingWithDeadlinesAndSetUpTimesWanted`), in which the set-up times are replaced by
changeover costs: no time is lost between tasks, and each change of compiler costs the changeover
cost of the compiler changed to, as the set-up time `l(k(t'))` of the parent is that of the
compiler of the later task. Bruno and Downey study single-machine sequencing of classes of tasks
with deadlines "in which there is a set-up time or a changeover cost associated with switching
from tasks in one class to another"; Garey and Johnson record that the changeover-cost problem is
NP-complete even if all changeover costs are equal, which is a special case of this one. No cost
is charged before the first task, as no set-up time is in the parent.

The instance extends the parent's: its first component lists the changeover costs `γ(c)` of the
compilers `c = 0, …, |C| - 1` (in the parent, their set-up times) and the tasks, task `t` being
the `t`-th triple `(l(t), d(t), k(t))`; the second component is `K`. The task accessors, the
one-processor schedules `IsOneProcessorSchedule` (Garey and Johnson's [SS1] notion) and
`SequencingWithDeadlinesAndSetUpTimes.WellFormed` (positive lengths and deadlines, compilers in
`C`) are the parent's. Since `σ` is one-to-one, each task has at most one direct predecessor, so
the total cost is the sum over tasks `t'` of `γ(k(t'))` when `t'` has a direct predecessor with a
different compiler. Binary encoding of all numbers (Garey and Johnson record that strong
NP-completeness is open).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SEQUENCING WITH DEADLINES AND CHANGEOVER COSTS is NP-complete.** Source: Garey and Johnson
(1979), [SS6], comment; Bruno and Downey (1978). -/
public theorem_wanted sequencingWithDeadlinesAndChangeoverCosts_npComplete :
    sequencingWithDeadlinesAndChangeoverCostsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingWithDeadlinesAndChangeoverCostsDec

end MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndChangeoverCosts
