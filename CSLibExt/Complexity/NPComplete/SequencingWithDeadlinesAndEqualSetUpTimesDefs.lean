/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING WITH DEADLINES AND SET-UP TIMES with equal set-up times: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS6] SEQUENCING WITH DEADLINES
AND SET-UP TIMES (comment: remains NP-complete even if all set-up times are equal);
J. Bruno and P. Downey, "Complexity of task sequencing with deadlines, set-up times and
changeover costs", SIAM Journal on Computing 7 (1978), 393-404, doi:10.1137/0207031.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SequencingWithDeadlinesAndSetUpTimesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndEqualSetUpTimes

/-- An instance, as in `SequencingWithDeadlinesAndSetUpTimesWanted`: the set-up times `l(c)` of
the compilers, and the tasks `(l(t), d(t), k(t))`. -/
abbrev SequencingWithDeadlinesAndEqualSetUpTimesInstance :=
  SequencingWithDeadlinesAndSetUpTimes.SequencingWithDeadlinesAndSetUpTimesInstance

/-- Well-formedness of an instance: the SEQUENCING WITH DEADLINES AND SET-UP TIMES instance is
well-formed and all set-up times are equal. -/
def WellFormed (i : SequencingWithDeadlinesAndEqualSetUpTimesInstance) : Prop :=
  SequencingWithDeadlinesAndSetUpTimes.WellFormed i ∧ ∀ a ∈ i.1, ∀ b ∈ i.1, a = b

/-- Some one-processor schedule meets every deadline and the set-up constraint, exactly as in
`SequencingWithDeadlinesAndSetUpTimesWanted`. -/
def SequencingWithDeadlinesAndEqualSetUpTimesFeasible
    (i : SequencingWithDeadlinesAndEqualSetUpTimesInstance) : Prop :=
  SequencingWithDeadlinesAndSetUpTimes.SequencingWithDeadlinesAndSetUpTimesFeasible i

open Classical in
/-- SEQUENCING WITH DEADLINES AND SET-UP TIMES with equal set-up times as a decision problem
over bitstrings. -/
noncomputable def sequencingWithDeadlinesAndEqualSetUpTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingWithDeadlinesAndEqualSetUpTimesInstance) x with
  | some i => decide (WellFormed i ∧ SequencingWithDeadlinesAndEqualSetUpTimesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SequencingWithDeadlinesAndEqualSetUpTimes
