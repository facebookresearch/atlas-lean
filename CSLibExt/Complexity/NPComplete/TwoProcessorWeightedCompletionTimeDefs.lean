/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorWeightedCompletionTime



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

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorWeightedCompletionTime
