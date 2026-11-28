/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POSITIVE ONE-IN-THREE 3SAT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO4] ONE-IN-THREE 3SAT (comment:
remains NP-complete if no clause contains a negated literal);
T. J. Schaefer, "The complexity of satisfiability problems", Proc. 10th Annual ACM Symposium on
Theory of Computing (STOC 1978), 216-226, doi:10.1145/800133.804350.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OneInThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PositiveOneInThreeSat

/-- Well-formedness of an instance: the parent's (three literals per clause, variables `< n`),
and every literal is positive. -/
def WellFormed (i : OneInThreeSat.OneInThreeSatInstance) : Prop :=
  OneInThreeSat.WellFormed i ∧ ∀ clause ∈ i.2, ∀ l ∈ clause, l.2 = true

open Classical in
/-- POSITIVE ONE-IN-THREE 3SAT as a decision problem over bitstrings. -/
noncomputable def positiveOneInThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OneInThreeSat.OneInThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ OneInThreeSat.OneInThreeSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PositiveOneInThreeSat
