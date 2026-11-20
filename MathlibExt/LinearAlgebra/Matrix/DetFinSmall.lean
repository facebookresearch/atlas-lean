/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Closed-form determinants of small integer matrices

`detFinThreeInt`, `detFinFourInt` and `detFinFiveInt` are cofactor expansions of the
determinant of a `3 × 3`, `4 × 4` and `5 × 5` integer matrix as explicit polynomials in the
entries, together with proofs that they agree with `Matrix.det`. They let `decide` and
`norm_num` evaluate such determinants without unfolding `Matrix.det`.

Extracted from the absolutely-maximally-entangled-state development now in
`PhyslibExt.QuantumInfo.AbsolutelyMaximallyEntangled`, where they are used to check that
every `5 × 5` cut matrix of a graph state is invertible modulo `5`.
-/

namespace MetaMathlibExt

/-- The Sarrus expansion of the determinant of a `3 × 3` integer matrix, as a
closed-form polynomial in the entries. -/
def detFinThreeInt (M : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
  M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0 -
  M 0 1 * M 1 0 * M 2 2 - M 0 0 * M 1 2 * M 2 1

/-- The determinant of a `4 × 4` integer matrix, expanded along the first row in terms
of `detFinThreeInt`. -/
def detFinFourInt (M : Matrix (Fin 4) (Fin 4) ℤ) : ℤ :=
  ∑ j : Fin 4, (-1) ^ (j : ℕ) * M 0 j *
    detFinThreeInt (M.submatrix (Fin.succAbove 0) (Fin.succAbove j))

/-- The determinant of a `5 × 5` integer matrix, expanded along the first row in terms
of `detFinFourInt`. -/
def detFinFiveInt (M : Matrix (Fin 5) (Fin 5) ℤ) : ℤ :=
  ∑ j : Fin 5, (-1) ^ (j : ℕ) * M 0 j *
    detFinFourInt (M.submatrix (Fin.succAbove 0) (Fin.succAbove j))

/-- `detFinThreeInt` computes the determinant of a `3 × 3` integer matrix. -/
lemma detFinThreeInt_eq (M : Matrix (Fin 3) (Fin 3) ℤ) :
    M.det = detFinThreeInt M := by
  rw [Matrix.det_fin_three]
  simp [detFinThreeInt]
  ring

/-- `detFinFourInt` computes the determinant of a `4 × 4` integer matrix. -/
lemma detFinFourInt_eq (M : Matrix (Fin 4) (Fin 4) ℤ) :
    M.det = detFinFourInt M := by
  rw [Matrix.det_succ_row M 0]
  apply Finset.sum_congr rfl
  intro j hj
  rw [detFinThreeInt_eq]
  simp [detFinFourInt]

/-- `detFinFiveInt` computes the determinant of a `5 × 5` integer matrix. -/
lemma detFinFiveInt_eq (M : Matrix (Fin 5) (Fin 5) ℤ) :
    M.det = detFinFiveInt M := by
  rw [Matrix.det_succ_row M 0]
  apply Finset.sum_congr rfl
  intro j hj
  rw [detFinFourInt_eq]
  simp [detFinFiveInt]

end MetaMathlibExt
