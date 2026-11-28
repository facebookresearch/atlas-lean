/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STACKER-CRANE with unit lengths: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE, comment;
G. N. Frederickson, M. S. Hecht and C. E. Kim, "Approximation algorithms for some routing
problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.StackerCraneDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StackerCraneUnitLengths

/-- Well-formedness of an instance: a well-formed STACKER-CRANE instance in which every
directed and every undirected edge has length `1`. -/
def WellFormed (i : StackerCrane.StackerCraneInstance) : Prop :=
  StackerCrane.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧ ∀ e ∈ i.2.2.1, e.2.2 = 1

open Classical in
/-- STACKER-CRANE with unit lengths as a decision problem over bitstrings. -/
noncomputable def stackerCraneUnitLengthsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StackerCrane.StackerCraneInstance) x with
  | some i => decide (WellFormed i ∧ StackerCrane.StackerCraneFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StackerCraneUnitLengths
