/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME on a fixed number `m ≥ 2` of
processors (`Pm|pmtn|Σw_iC_i`) is NP-complete

Source:
R. McNaughton, "Scheduling with deadlines and loss functions", Management Science 6 (1959),
1-12, doi:10.1287/mnsc.6.1.1;
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (Theorem 3(b) for `m = 2`, Theorem 1(c) for `m ≥ 2`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS13], comment;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(`Pm|pmtn|Σw_iC_i`, maximal pseudo-polynomially solvable, citing McNaughton 1959).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PreemptiveParallelFixedMachinesWeightedCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PreemptiveParallelFixedMachinesWeightedCompletionTime

open SchedulingToMinimizeWeightedCompletionTime
  (SchedulingToMinimizeWeightedCompletionTimeInstance)
open PreemptiveWeightedCompletionTime (PreemptiveWeightedCompletionTimeFeasible)
open ParallelFixedMachinesWeightedCompletionTime (WellFormed)

/-!
# PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME on `m` processors, `m ≥ 2` fixed,
is NP-complete

For a fixed number `m ≥ 2` of processors: INSTANCE: a set `T` of tasks, for each task `t ∈ T` a
length `l(t) ∈ ℤ⁺` and a weight `w(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there an
`m`-processor preemptive schedule for `T` such that the sum, over all `t ∈ T`, of the completion
time of `t` times `w(t)` is no more than `K`?

This is `Pm|pmtn|Σw_iC_i`, the restriction of PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED
COMPLETION TIME (`WantedExt.Complexity.NPComplete.PreemptiveWeightedCompletionTimeWanted`) to `m`
processors, one decision problem for each fixed `m`. The instance type and the question
(preemptive schedules as lists of pieces per task) are that module's, and the well-formedness
condition is `ParallelFixedMachinesWeightedCompletionTime.WellFormed m` of the nonpreemptive
`Pm||Σw_iC_i` (`ParallelFixedMachinesWeightedCompletionTimeWanted`): a well-formed SCHEDULING TO
MINIMIZE WEIGHTED COMPLETION TIME instance (`0 < m`, positive lengths and weights, `0 < K`) with
exactly `m` processors, tasks listed one per entry. McNaughton proves that on identical
processors preemption does not decrease the weighted sum of completion times, so a preemptive
schedule meeting `K` exists exactly when a nonpreemptive one does, and the problem is equivalent
to `Pm||Σw_iC_i`; for that problem Lenstra, Rinnooy Kan and Brucker reduce PARTITION to the case
`m = 2` (Theorem 3(b)), and their Theorem 1(c) reduces a problem on `m'` machines to the same
problem on `m ≥ m'` machines.
Membership in NP follows from the same equivalence: the certificate is a nonpreemptive schedule
(one piece per task), with start times at most `K`. Binary encoding of all numbers: for fixed
`m` the problem is solvable in pseudo-polynomial time, so it is NP-complete only in the ordinary
sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete for every fixed
number `m ≥ 2` of processors (`Pm|pmtn|Σw_iC_i`).** Source: McNaughton (1959); Lenstra,
Rinnooy Kan and Brucker (1977), Theorems 3(b) and 1(c); Garey and Johnson (1979), [SS13],
comment. -/
public theorem_wanted preemptiveParallelFixedMachinesWeightedCompletionTime_npComplete (m : ℕ)
    (hm : 2 ≤ m) :
    preemptiveParallelFixedMachinesWeightedCompletionTimeDec m ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L
            (preemptiveParallelFixedMachinesWeightedCompletionTimeDec m)

end MetaMathlibExt.Complexity.NPComplete.PreemptiveParallelFixedMachinesWeightedCompletionTime
