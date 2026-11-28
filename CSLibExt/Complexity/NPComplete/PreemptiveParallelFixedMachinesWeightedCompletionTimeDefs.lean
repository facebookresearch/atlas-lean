/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PREEMPTIVE SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME on a fixed number `m ≥ 2` of processors
(`Pm|pmtn|Σw_iC_i`): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ParallelFixedMachinesWeightedCompletionTimeDefs
public import CSLibExt.Complexity.NPComplete.PreemptiveWeightedCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PreemptiveParallelFixedMachinesWeightedCompletionTime

open SchedulingToMinimizeWeightedCompletionTime
  (SchedulingToMinimizeWeightedCompletionTimeInstance)
open PreemptiveWeightedCompletionTime (PreemptiveWeightedCompletionTimeFeasible)
open ParallelFixedMachinesWeightedCompletionTime (WellFormed)

open Classical in
/-- `Pm|pmtn|Σw_iC_i` for the fixed number `m` of processors, as a decision problem over
bitstrings. -/
noncomputable def preemptiveParallelFixedMachinesWeightedCompletionTimeDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SchedulingToMinimizeWeightedCompletionTimeInstance) x with
  | some i => decide (WellFormed m i ∧ PreemptiveWeightedCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PreemptiveParallelFixedMachinesWeightedCompletionTime
