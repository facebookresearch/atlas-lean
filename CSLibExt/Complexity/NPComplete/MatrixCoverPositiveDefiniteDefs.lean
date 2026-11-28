/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATRIX COVER with a positive definite matrix: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 282, problem [MS13] MATRIX COVER (comment:
"NP-complete in the strong sense and remains so if A is required to be positive definite.";
credited there to Garey and Johnson, unpublished; transformation from MAX CUT), with the
comparison `≤ K` of the parent module `MatrixCoverWanted` (see its docstring).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MatrixCoverDefs
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatrixCoverPositiveDefinite

open MetaMathlibExt.Complexity.NPComplete.MatrixCover (MatrixCoverInstance MatrixCoverFeasible)

/-- The matrix `A` of the instance, with real entries, indexed by `Fin n`. -/
def realMatrix (i : MatrixCoverInstance) : Matrix (Fin i.1) (Fin i.1) ℝ :=
  Matrix.of fun r c => ((i.2.1.getD r []).getD c 0 : ℝ)

/-- Well-formedness of an instance: the [MS13] well-formedness, and `A` is positive definite
(Mathlib's `Matrix.PosDef`: symmetric, and `xᵀ A x > 0` for every nonzero real vector `x`). -/
def WellFormed (i : MatrixCoverInstance) : Prop :=
  MatrixCover.WellFormed i ∧ (realMatrix i).PosDef

open Classical in
/-- MATRIX COVER with a positive definite matrix as a decision problem over bitstrings. -/
noncomputable def matrixCoverPositiveDefiniteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatrixCoverInstance) x with
  | some i => decide (WellFormed i ∧ MatrixCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MatrixCoverPositiveDefinite
