/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.RowCol

import Mathlib.Tactic.Ring

/-!
# The matrix determinant lemma, without an invertibility hypothesis

Mathlib proves the matrix determinant lemma under the hypothesis that
`A.det` is a unit (`Matrix.det_add_replicateCol_mul_replicateRow`), and
leaves the general version as a TODO:

> TODO: show the more general version without `hA : IsUnit A.det` as
> `(A + replicateCol u * replicateRow v).det = A.det + v ⬝ᵥ (adjugate A) *ᵥ u`.

This file proves that general version, over any commutative ring. The proof
expands the determinant row by row: replacing one row of `A` by the
corresponding row of `A + vecMulVec u v` adds `u i * det (A.updateRow i v)`
(because the other rows differ from those of `A` only by multiples of the
replaced row, which does not change the determinant, by
`Matrix.det_eq_of_forall_row_eq_smul_add_const`), and summing those terms
gives the `adjugate` pairing by Cramer's rule
(`Matrix.cramer_transpose_apply`, `Matrix.cramer_eq_adjugate_mulVec`) and
the bilinear-form identity `Matrix.dotProduct_transpose_mulVec`. The same
argument also gives the invertibility criterion for a rank-one update, with
no invertibility hypothesis on `A`.
-/

@[expose] public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- Summing the one-row expansions over all rows gives the adjugate pairing:
`∑ i, u i * det (A.updateRow i v) = v ⬝ᵥ (adjugate A *ᵥ u)`. By Cramer's
rule (`Matrix.cramer_transpose_apply`, `Matrix.cramer_eq_adjugate_mulVec`)
the one-row determinant is a component of `adjugate Aᵀ *ᵥ v`, and the
bilinear-form identity `Matrix.dotProduct_transpose_mulVec` swaps the
two sides. -/
private theorem sum_mul_det_updateRow (A : Matrix n n R) (u v : n → R) :
    ∑ i, u i * (A.updateRow i v).det = v ⬝ᵥ (adjugate A *ᵥ u) := by
  have key : ∀ i, (A.updateRow i v).det = (adjugate Aᵀ *ᵥ v) i := fun i => by
    rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec]
  simp only [key]
  have hdot : ∑ i, u i * (adjugate Aᵀ *ᵥ v) i = u ⬝ᵥ (adjugate Aᵀ *ᵥ v) := rfl
  rw [hdot, ← adjugate_transpose]
  exact dotProduct_transpose_mulVec (adjugate A) u v

/-- Expanding the determinant row by row: if the rows indexed by `S` of `A`
are replaced by the corresponding rows of `A + vecMulVec u v`, the
determinant picks up one summand `u i * det (A.updateRow i v)` per replaced
row. -/
private theorem det_eq_det_add_sum_updateRow (A : Matrix n n R) (u v : n → R)
    (S : Finset n) :
    (Matrix.of fun i j => if i ∈ S then (A + vecMulVec u v) i j else A i j).det =
      A.det + ∑ i ∈ S, u i * (A.updateRow i v).det := by
  induction S using Finset.induction_on with
  | empty =>
    have hM : (Matrix.of fun i j =>
        if i ∈ (∅ : Finset n) then (A + vecMulVec u v) i j else A i j) = A := by
      ext i j
      simp
    rw [hM, Finset.sum_empty, add_zero]
  | @insert i S hi ih =>
    have hM : (Matrix.of fun i' j =>
        if i' ∈ insert i S then (A + vecMulVec u v) i' j else A i' j) =
        updateRow (Matrix.of fun i' j =>
          if i' ∈ S then (A + vecMulVec u v) i' j else A i' j) i
          ((Matrix.of fun i' j =>
            if i' ∈ S then (A + vecMulVec u v) i' j else A i' j) i + u i • v) := by
      ext j k
      by_cases hj : j = i
      · subst hj
        simp [updateRow_self, hi, vecMulVec_apply]
      · simp [hj]
    have hrow : (updateRow (Matrix.of fun i' j =>
        if i' ∈ S then (A + vecMulVec u v) i' j else A i' j) i v).det =
        (A.updateRow i v).det := by
      apply det_eq_of_forall_row_eq_smul_add_const (fun j => if j ∈ S then u j else 0) i
      · simp [hi]
      · intro j k
        by_cases hj : j = i
        · subst hj
          simp [hi]
        · rw [updateRow_ne hj, updateRow_ne hj, updateRow_self]
          by_cases hjS : j ∈ S
          · simp [hjS, add_apply, vecMulVec_apply]
          · simp [hjS]
    rw [hM, det_updateRow_add, updateRow_eq_self, det_updateRow_smul, hrow, ih,
      Finset.sum_insert hi]
    ring

/-- The **matrix determinant lemma**, without any invertibility hypothesis:
the determinant of a rank-one update of `A` is `det A` plus the adjugate
pairing `v ⬝ᵥ (adjugate A *ᵥ u)`. This is the general version left as a TODO
in Mathlib's `Matrix.det_add_replicateCol_mul_replicateRow`. -/
theorem det_add_vecMulVec (A : Matrix n n R) (u v : n → R) :
    (A + vecMulVec u v).det = A.det + v ⬝ᵥ (adjugate A *ᵥ u) := by
  have hM : (Matrix.of fun i j =>
      if i ∈ (Finset.univ : Finset n) then (A + vecMulVec u v) i j else A i j) =
      A + vecMulVec u v := by
    ext i j
    simp
  rw [← hM, det_eq_det_add_sum_updateRow]
  congr 1
  exact sum_mul_det_updateRow A u v

/-- The matrix determinant lemma in the `replicateCol` / `replicateRow`
form stated in Mathlib's TODO for
`Matrix.det_add_replicateCol_mul_replicateRow`. The `_general` suffix
avoids clashing with Mathlib's invertible version of the same name. -/
theorem det_add_replicateCol_mul_replicateRow_general {ι : Type*} [Unique ι]
    (A : Matrix n n R) (u v : n → R) :
    (A + replicateCol ι u * replicateRow ι v).det =
      A.det + v ⬝ᵥ (adjugate A *ᵥ u) := by
  rw [← vecMulVec_eq ι u v]
  exact det_add_vecMulVec A u v

/-- A rank-one update of `A` is a unit exactly when the adjugate correction
term is a unit; no invertibility hypothesis on `A` is needed. -/
theorem isUnit_add_vecMulVec_iff (A : Matrix n n R) (u v : n → R) :
    IsUnit (A + vecMulVec u v) ↔
      IsUnit (A.det + v ⬝ᵥ (adjugate A *ᵥ u)) := by
  rw [isUnit_iff_isUnit_det, det_add_vecMulVec]

/-- The matrix determinant lemma in multiplicative form, when `A.det` is a
unit: this recovers Mathlib's
`Matrix.det_add_replicateCol_mul_replicateRow` from the general version. -/
theorem det_add_vecMulVec_of_isUnit_det (A : Matrix n n R) (u v : n → R)
    (hA : IsUnit A.det) :
    (A + vecMulVec u v).det = A.det * (1 + v ⬝ᵥ A⁻¹ *ᵥ u) := by
  have hadj : adjugate A = A.det • A⁻¹ := by
    have hmul := congrArg (· * A⁻¹) (adjugate_mul A)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hA, Matrix.mul_one] at hmul
    rw [hmul, smul_mul_assoc, Matrix.one_mul]
  rw [det_add_vecMulVec, hadj, smul_mulVec, dotProduct_smul]
  ring

end Matrix
