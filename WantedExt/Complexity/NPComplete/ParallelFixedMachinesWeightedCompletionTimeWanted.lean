/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME on a fixed number `m ≥ 2` of processors
(`Pm||Σw_iC_i`) is NP-complete

Source:
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X (Theorem 3(b) for `m = 2`, Theorem 1(c) for `m ≥ 2`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS13], comment;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(`Pm||Σw_iC_i`, maximal pseudo-polynomially solvable; `P2||Σw_iC_i` NP-hard).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ParallelFixedMachinesWeightedCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelFixedMachinesWeightedCompletionTime

open SchedulingToMinimizeWeightedCompletionTime
  (SchedulingToMinimizeWeightedCompletionTimeInstance
    SchedulingToMinimizeWeightedCompletionTimeFeasible)

/-!
# SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME on `m` processors, `m ≥ 2` fixed, is
NP-complete

For a fixed number `m ≥ 2` of processors: INSTANCE: a set `T` of tasks, for each task `t ∈ T` a
length `l(t) ∈ ℤ⁺` and a weight `w(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there an
`m`-processor schedule `σ` for `T` such that the sum, over all `t ∈ T`, of `(σ(t) + l(t)) · w(t)`
is no more than `K`?

This is `Pm||Σw_iC_i`, the restriction of SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME
(`WantedExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeWanted`) to `m`
processors, one decision problem for each fixed `m`. The instance type, the parent
well-formedness condition and the question are that module's
(`SchedulingToMinimizeWeightedCompletionTime.SchedulingToMinimizeWeightedCompletionTimeInstance`,
`SchedulingToMinimizeWeightedCompletionTime.WellFormed`,
`SchedulingToMinimizeWeightedCompletionTime.SchedulingToMinimizeWeightedCompletionTimeFeasible`);
the restriction to the fixed `m` is added to `WellFormed`, so tasks are listed one per entry. For
`m = 2` this is `TwoProcessorWeightedCompletionTimeWanted`. Lenstra, Rinnooy Kan and Brucker
reduce PARTITION to the case `m = 2` (Theorem 3(b), after Bruno, Coffman and Sethi), and their
Theorem 1(c) reduces a problem on `m'` machines to the same problem on `m ≥ m'` machines. Binary
encoding of all numbers: for fixed `m` the problem is solvable in pseudo-polynomial time, so it
is NP-complete only in the ordinary sense.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete for every fixed number
`m ≥ 2` of processors (`Pm||Σw_iC_i`).** Source: Lenstra, Rinnooy Kan and Brucker (1977),
Theorems 3(b) and 1(c); Garey and Johnson (1979), [SS13], comment. -/
public theorem_wanted parallelFixedMachinesWeightedCompletionTime_npComplete (m : ℕ)
    (hm : 2 ≤ m) :
    parallelFixedMachinesWeightedCompletionTimeDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (parallelFixedMachinesWeightedCompletionTimeDec m)

end MetaMathlibExt.Complexity.NPComplete.ParallelFixedMachinesWeightedCompletionTime
