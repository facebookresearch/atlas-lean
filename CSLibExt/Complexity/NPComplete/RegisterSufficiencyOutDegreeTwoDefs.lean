/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGISTER SUFFICIENCY (out-degree at most 2): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO1] REGISTER
SUFFICIENCY (comment: remains NP-complete even if all vertices of `G` have
out-degree 2 or less);
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4
(1975), 226-248, doi:10.1137/0204020.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RegisterSufficiencyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegisterSufficiencyOutDegreeTwo

/-- Well-formedness of an instance: a well-formed REGISTER SUFFICIENCY instance in which every
vertex is the tail of at most two arcs. -/
def WellFormed (i : RegisterSufficiency.RegisterSufficiencyInstance) : Prop :=
  RegisterSufficiency.WellFormed i ∧ ∀ a ∈ i.2.1, i.2.1.countP (fun b => b.1 = a.1) ≤ 2

open Classical in
/-- REGISTER SUFFICIENCY (out-degree at most 2) as a decision problem over bitstrings. -/
noncomputable def registerSufficiencyOutDegreeTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RegisterSufficiency.RegisterSufficiencyInstance) x with
  | some i => decide (WellFormed i ∧ RegisterSufficiency.RegisterSufficiencyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RegisterSufficiencyOutDegreeTwo
