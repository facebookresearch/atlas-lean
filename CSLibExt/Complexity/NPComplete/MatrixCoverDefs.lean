/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATRIX COVER: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 282, problem [MS13] MATRIX
COVER (credited there to Garey and Johnson, unpublished; transformation from
MAX CUT), with the comparison reversed: the entry prints `≥ K`, and this module
states `≤ K`, the question that the cited MAX CUT transformation proves
NP-hard (see the module docstring). The `≤ K` reading, with the target
`K' = 2(|E| - 2K)` for a MAX CUT bound `K`, is the one in S. McCulloch,
"Discussions of NP-Complete Problems", entry for MS13 Matrix Cover,
https://npcomplete.owu.edu/.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatrixCover

/-- An instance: the side length `n`, the matrix `A` as a list of rows, and the bound `K` as a
pair `(K.1, K.2)` standing for the integer `K.1 - K.2`. -/
abbrev MatrixCoverInstance := ℕ × List (List ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: `A` has `n` rows of length `n`. -/
def WellFormed (i : MatrixCoverInstance) : Prop :=
  i.2.1.length = i.1 ∧ ∀ row ∈ i.2.1, row.length = i.1

/-- A sign function `f` (values `1` or `-1` on `0, ..., n - 1`) with
`∑_{r, c < n} A r c * f r * f c ≤ K`. -/
def MatrixCoverFeasible (i : MatrixCoverInstance) : Prop :=
  ∃ f : ℕ → ℤ, (∀ j < i.1, f j = 1 ∨ f j = -1) ∧
    ∑ r ∈ Finset.range i.1, ∑ c ∈ Finset.range i.1,
        ((i.2.1.getD r []).getD c 0 : ℤ) * f r * f c ≤ (i.2.2.1 : ℤ) - i.2.2.2

open Classical in
/-- MATRIX COVER as a decision problem over bitstrings. -/
noncomputable def matrixCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatrixCoverInstance) x with
  | some i => decide (WellFormed i ∧ MatrixCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MatrixCover
