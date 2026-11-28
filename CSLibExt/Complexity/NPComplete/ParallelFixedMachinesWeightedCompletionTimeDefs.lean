/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME on a fixed number `m ≥ 2` of processors
(`Pm||Σw_iC_i`): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SchedulingToMinimizeWeightedCompletionTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelFixedMachinesWeightedCompletionTime

open SchedulingToMinimizeWeightedCompletionTime
  (SchedulingToMinimizeWeightedCompletionTimeInstance
    SchedulingToMinimizeWeightedCompletionTimeFeasible)

/-- Well-formedness of an instance for the fixed number `m` of processors: it is a well-formed
SCHEDULING TO MINIMIZE WEIGHTED COMPLETION TIME instance (`0 < m`, positive lengths and
weights, `0 < K`) with exactly `m` processors. -/
def WellFormed (m : ℕ) (i : SchedulingToMinimizeWeightedCompletionTimeInstance) : Prop :=
  SchedulingToMinimizeWeightedCompletionTime.WellFormed i ∧ i.1 = m

open Classical in
/-- `Pm||Σw_iC_i` for the fixed number `m` of processors, as a decision problem over
bitstrings. -/
noncomputable def parallelFixedMachinesWeightedCompletionTimeDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SchedulingToMinimizeWeightedCompletionTimeInstance) x with
  | some i => decide (WellFormed m i ∧ SchedulingToMinimizeWeightedCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ParallelFixedMachinesWeightedCompletionTime
