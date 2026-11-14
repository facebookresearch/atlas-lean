/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATRIX COVER with a positive definite matrix is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 282, problem [MS13] MATRIX COVER (comment:
"NP-complete in the strong sense and remains so if A is required to be positive definite.";
credited there to Garey and Johnson, unpublished; transformation from MAX CUT), with the
comparison `≤ K` of the parent module `MatrixCoverWanted` (see its docstring).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MatrixCoverWanted
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatrixCoverPositiveDefinite

open MetaMathlibExt.Complexity.NPComplete.MatrixCover (MatrixCoverInstance MatrixCoverFeasible)

/-!
# MATRIX COVER with a positive definite matrix is NP-complete

MATRIX COVER ([MS13], `MatrixCoverWanted`) restricted to positive definite matrices.
INSTANCE: an `n × n` matrix `A = (a i j)` with nonnegative integer entries that is positive
definite, and an integer `K`. QUESTION: is there a function `f : {1, ..., n} → {-1, +1}` such
that `∑_{1 ≤ i, j ≤ n} a i j * f i * f j ≤ K`?

The instance and the question (with the comparison `≤`, as in `MatrixCoverWanted`) are those of
the parent; only the restriction is new, in `WellFormed`: `A`, read as a real matrix, is
positive definite in Mathlib's sense (`Matrix.PosDef`), i.e. symmetric with `xᵀ A x > 0` for
every nonzero real vector `x`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MATRIX COVER with a positive definite matrix is NP-complete.** Source: Garey and Johnson
(1979), [MS13], comment. -/
public theorem_wanted matrixCoverPositiveDefinite_npComplete :
    matrixCoverPositiveDefiniteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L matrixCoverPositiveDefiniteDec

end MetaMathlibExt.Complexity.NPComplete.MatrixCoverPositiveDefinite
