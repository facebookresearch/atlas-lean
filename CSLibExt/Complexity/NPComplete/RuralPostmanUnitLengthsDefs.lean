/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RURAL POSTMAN with unit lengths: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN, comment
(p. 213: "Remains NP-complete even if l(e) = 1 for all e ∈ E");
J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems",
Networks 6 (1976), 273-280, doi:10.1002/net.3230060305 (the entry's reference).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RuralPostmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RuralPostmanUnitLengths

open MetaMathlibExt.Complexity.NPComplete.RuralPostman
  (RuralPostmanInstance RuralPostmanFeasible)

/-- Well-formedness of an instance: the parent's (simple edge list, required edges in the graph,
`0 < B`) and every edge length is `1`. -/
def WellFormed (i : RuralPostmanInstance) : Prop :=
  RuralPostman.WellFormed i ∧ ∀ e ∈ i.2.1, e.2.2 = 1

open Classical in
/-- RURAL POSTMAN with unit lengths as a decision problem over bitstrings. -/
noncomputable def ruralPostmanUnitLengthsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RuralPostmanInstance) x with
  | some i => decide (WellFormed i ∧ RuralPostmanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RuralPostmanUnitLengths
