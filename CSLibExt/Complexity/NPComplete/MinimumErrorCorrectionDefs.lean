/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM ERROR CORRECTION (single individual SNP haplotyping): definitions

Source:
R. Cilibrasi, L. van Iersel, S. Kelk and J. Tromp, "The complexity of the single individual
SNP haplotyping problem", Algorithmica 49 (2007), 13-36, doi:10.1007/s00453-007-0029-z,
arXiv:q-bio/0508012, Section II.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumErrorCorrection

/-- An instance: the number `m` of columns (SNP sites), the rows (fragments) of the SNP matrix
with entries `0`, `1`, or `2` for a hole, and the bound `K`. -/
abbrev MinimumErrorCorrectionInstance := ℕ × List (List ℕ) × ℕ

/-- `d(X, Y)`: the number of positions `j < m` where the entry `x` of the row `X` (read as `2`
beyond its length) is not `2` and `x = 1` differs from the haplotype value `Y j`. Holes (`2`)
do not count; every other entry, `0` or a value above `2`, is read as `false` unless it is `1`.
-/
def mismatches {m : ℕ} (X : List ℕ) (Y : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun j : Fin m => X.getD j 2 ≠ 2 ∧ decide (X.getD j 2 = 1) ≠ Y j).card

/-- Well-formedness of an instance: every row has length `m` and entries in `{0, 1, 2}`. -/
def WellFormed (i : MinimumErrorCorrectionInstance) : Prop :=
  ∀ r ∈ i.2.1, r.length = i.1 ∧ ∀ x ∈ r, x ≤ 2

/-- At most `K` flips make the matrix feasible: there are haplotypes `H₁`, `H₂` and an
assignment `side` of the rows to them with total mismatch count at most `K`. -/
def MinimumErrorCorrectionFeasible (i : MinimumErrorCorrectionInstance) : Prop :=
  ∃ H₁ H₂ : Fin i.1 → Bool, ∃ side : Fin i.2.1.length → Bool,
    (∑ r : Fin i.2.1.length, mismatches (i.2.1.get r) (if side r then H₂ else H₁)) ≤ i.2.2

open Classical in
/-- MINIMUM ERROR CORRECTION as a decision problem over bitstrings. -/
noncomputable def minimumErrorCorrectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumErrorCorrectionInstance) x with
  | some i => decide (WellFormed i ∧ MinimumErrorCorrectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumErrorCorrection
