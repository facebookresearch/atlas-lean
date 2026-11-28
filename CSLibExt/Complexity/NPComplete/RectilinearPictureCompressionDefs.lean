/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR PICTURE COMPRESSION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR25] RECTILINEAR PICTURE
COMPRESSION, p. 232 (reference [Masek, 1978]: W. J. Masek, "Some NP-complete set covering
problems", unpublished manuscript, as listed in Garey and Johnson's references; transformation
from 3SAT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearPictureCompression

/-- An instance: the rows of the matrix `M` (`true` for an entry `1`) and the bound `K`. -/
abbrev RectilinearPictureCompressionInstance := List (List Bool) × ℕ

/-- The entry `M_{ij}` (`0`-based), read as `false` outside the matrix. -/
def entry (M : List (List Bool)) (i j : ℕ) : Bool := (M.getD i []).getD j false

/-- Well-formedness of an instance: `M` is square (every row has `n` entries, where `n` is the
number of rows), and `K` is positive. -/
def WellFormed (i : RectilinearPictureCompressionInstance) : Prop :=
  (∀ row ∈ i.1, row.length = i.1.length) ∧ 0 < i.2

/-- Some list of at most `K` rectangles `[a, b] × [c, d]` with `a ≤ b`, `c ≤ d` covers exactly
the entries `1` of `M`. -/
def RectilinearPictureCompressionFeasible (i : RectilinearPictureCompressionInstance) : Prop :=
  ∃ R : List (ℕ × ℕ × ℕ × ℕ), R.length ≤ i.2 ∧ (∀ r ∈ R, r.1 ≤ r.2.1 ∧ r.2.2.1 ≤ r.2.2.2) ∧
    ∀ a < i.1.length, ∀ b < i.1.length,
      (entry i.1 a b = true ↔ ∃ r ∈ R, r.1 ≤ a ∧ a ≤ r.2.1 ∧ r.2.2.1 ≤ b ∧ b ≤ r.2.2.2)

open Classical in
/-- RECTILINEAR PICTURE COMPRESSION as a decision problem over bitstrings. -/
noncomputable def rectilinearPictureCompressionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectilinearPictureCompressionInstance) x with
  | some i => decide (WellFormed i ∧ RectilinearPictureCompressionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RectilinearPictureCompression
