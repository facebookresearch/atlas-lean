/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATRIX DOMINATION for upper triangular matrices: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS12] MATRIX DOMINATION, comment:
remains NP-complete when `M` is upper triangular;
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on Applied
Mathematics 38 (1980), 364-372, doi:10.1137/0138030 (the reference Garey and Johnson give for
[MS12]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MatrixDominationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatrixDominationUpperTriangular

open MetaMathlibExt.Complexity.NPComplete.MatrixDomination

/-- The matrix is upper triangular: every entry below the main diagonal is `0`, i.e., every
non-zero entry `(r, c)` has `r ≤ c`. -/
def UpperTriangular (i : MatrixDominationInstance) : Prop :=
  ∀ r c, Entry i r c → r ≤ c

open Classical in
/-- MATRIX DOMINATION for upper triangular matrices as a decision problem over bitstrings. -/
noncomputable def matrixDominationUpperTriangularDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatrixDominationInstance) x with
  | some i => decide (WellFormed i ∧ UpperTriangular i ∧ MatrixDominationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MatrixDominationUpperTriangular
