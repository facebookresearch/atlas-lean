/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET BASIS with sets of size at most 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 222, problem [SP7] SET BASIS
(comment: remains NP-complete if all `c ∈ C` have `|c| ≤ 3`);
L. J. Stockmeyer, "The set basis problem is NP-complete", Report RC-5431,
IBM Research Center, Yorktown Heights, NY (1975).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SetBasisDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetBasisSizeThree

open MetaMathlibExt.Complexity.NPComplete.SetBasis

/-- Well-formedness of an instance: it is a well-formed SET BASIS instance (strictly
increasing lists of elements of `S`, no member listed twice, `0 < K ≤ |C|`) and every member of
`C` has at most three elements. -/
def WellFormed (i : SetBasisInstance) : Prop :=
  SetBasis.WellFormed i ∧ ∀ c ∈ i.2.1, c.length ≤ 3

open Classical in
/-- SET BASIS with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def setBasisSizeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetBasisInstance) x with
  | some i => decide (WellFormed i ∧ SetBasisFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SetBasisSizeThree
