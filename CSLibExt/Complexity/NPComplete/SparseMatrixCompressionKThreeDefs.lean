/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SPARSE MATRIX COMPRESSION with K = 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), p. 229, problem [SR13] SPARSE MATRIX COMPRESSION
(comment: remains NP-complete for fixed `K = 3`; reference: [Even, Lichtenstein, and
Shiloach, 1977]);
S. Even, D. I. Lichtenstein and Y. Shiloach, "Remarks on Ziegler's method for matrix
compression", unpublished manuscript (1977);
V. Jugé, D. Köppl, V. Limouzy, A. Marino, J. Olblich, G. Punzi and T. Uno, "Revisiting the
sparse matrix compression problem", arXiv:2602.15314 (2026), Section 1 (records that the
problem is NP-complete even if the maximum needed shift is at most two).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SparseMatrixCompressionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompressionKThree

open MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompression

/-- Well-formedness of an instance: it is a well-formed SPARSE MATRIX COMPRESSION instance
(every row has `n` entries, `0 < K ≤ mn`) and `K = 3`. -/
def WellFormed (i : SparseMatrixCompressionInstance) : Prop :=
  SparseMatrixCompression.WellFormed i ∧ i.2.2 = 3

open Classical in
/-- SPARSE MATRIX COMPRESSION with `K = 3` as a decision problem over bitstrings. -/
noncomputable def sparseMatrixCompressionKThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SparseMatrixCompressionInstance) x with
  | some i => decide (WellFormed i ∧ SparseMatrixCompressionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SparseMatrixCompressionKThree
