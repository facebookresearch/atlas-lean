/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS13] SCHEDULING TO MINIMIZE
WEIGHTED COMPLETION TIME, comment: remains NP-complete for `m = 2`;
J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X;
J. Bruno, E. G. Coffman, Jr. and R. Sethi, "Scheduling independent tasks to reduce mean
finishing time", Communications of the ACM 17 (1974), 382-387, doi:10.1145/361011.361064.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorWeightedCompletionTime

/-!
# TWO-PROCESSOR SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete

INSTANCE: a set `T` of tasks, `m = 2` processors, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺` and
a weight `w(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a 2-processor schedule `σ`
for `T` such that the sum, over all `t ∈ T`, of `(σ(t) + l(t)) · w(t)` is no more than `K`?

This is the restriction of SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME
(`WantedExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeWanted`) to `m = 2`.
The instance type, the parent well-formedness condition and the question are that module's
(`SchedulingToMinimizeWeightedCompletionTime.SchedulingToMinimizeWeightedCompletionTimeInstance`,
`SchedulingToMinimizeWeightedCompletionTime.WellFormed`,
`SchedulingToMinimizeWeightedCompletionTime.SchedulingToMinimizeWeightedCompletionTimeFeasible`);
the restriction is added to `WellFormed`. Binary encoding of all numbers: for `m = 2` the problem
is NP-complete but solvable in pseudo-polynomial time, so it is not NP-complete in the strong
sense unless P = NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open SchedulingToMinimizeWeightedCompletionTime
  (SchedulingToMinimizeWeightedCompletionTimeInstance
    SchedulingToMinimizeWeightedCompletionTimeFeasible)

/-- Well-formedness of an instance: it is a well-formed SCHEDULING TO MINIMIZE WEIGHTED
COMPLETION TIME instance (`0 < m`, positive lengths and weights, `0 < K`) with `m = 2`
processors. -/
def WellFormed (i : SchedulingToMinimizeWeightedCompletionTimeInstance) : Prop :=
  SchedulingToMinimizeWeightedCompletionTime.WellFormed i ∧ i.1 = 2

open Classical in
/-- TWO-PROCESSOR SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME as a decision problem over
bitstrings. -/
noncomputable def twoProcessorWeightedCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SchedulingToMinimizeWeightedCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ SchedulingToMinimizeWeightedCompletionTimeFeasible i)
  | none => false

/-- **TWO-PROCESSOR SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME is NP-complete.** Source:
Garey and Johnson (1979), [SS13], comment; Lenstra, Rinnooy Kan and Brucker (1977); Bruno,
Coffman and Sethi (1974). -/
public theorem_wanted twoProcessorWeightedCompletionTime_npComplete :
    twoProcessorWeightedCompletionTimeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorWeightedCompletionTimeDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorWeightedCompletionTime
