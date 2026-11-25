/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import MathlibExt.LinearAlgebra.Matrix.ZeroExtension

/-!
# Zero padding in the supremum-of-row-sums seminorm

Let the coefficients form a seminormed additive commutative group, and let
`r ≤ s` be natural matrix sizes. Extend an `r`-by-`r` matrix to an
`s`-by-`s` matrix by keeping its top-left block and inserting zero in every
new row or column. The seminorm `max_i sum_j ‖Xᵢⱼ‖` is preserved, using
exactly the displayed outer-supremum and inner-L1 matrix seminorm structures.

The empty matrix and zero coefficients are included. No coefficient ring,
scalar action, associativity of multiplication or completeness is required.
-/

public section

open scoped BigOperators NNReal

namespace Matrix

universe u

/-- For `r ≤ s`, top-left zero extension preserves the matrix seminorm `max_i sum_j ‖Xᵢⱼ‖`, using
the displayed outer-supremum/inner-L1 seminorm structures. This includes `r=0` and requires only
seminormed additive coefficients.

```lean
theorem linfty_opNorm_zeroExtend
    {A : Type u} [SeminormedAddCommGroup A]
    {r s : ℕ} (h : r ≤ s) (X : Matrix (Fin r) (Fin r) A) :
    letI : SeminormedAddCommGroup (Matrix (Fin r) (Fin r) A) :=
      Matrix.linftyOpSeminormedAddCommGroup
    letI : SeminormedAddCommGroup (Matrix (Fin s) (Fin s) A) :=
      Matrix.linftyOpSeminormedAddCommGroup
    ‖Matrix.zeroExtend h X‖ = ‖X‖
``` -/
theorem linfty_opNorm_zeroExtend
    {A : Type u} [SeminormedAddCommGroup A]
    {r s : ℕ} (h : r ≤ s) (X : Matrix (Fin r) (Fin r) A) :
    letI : SeminormedAddCommGroup (Matrix (Fin r) (Fin r) A) :=
      Matrix.linftyOpSeminormedAddCommGroup
    letI : SeminormedAddCommGroup (Matrix (Fin s) (Fin s) A) :=
      Matrix.linftyOpSeminormedAddCommGroup
    ‖Matrix.zeroExtend h X‖ = ‖X‖ := by
  classical
  let _ : SeminormedAddCommGroup (Matrix (Fin r) (Fin r) A) :=
    Matrix.linftyOpSeminormedAddCommGroup
  let _ : SeminormedAddCommGroup (Matrix (Fin s) (Fin s) A) :=
    Matrix.linftyOpSeminormedAddCommGroup
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  let Z : Matrix (Fin (r + d)) (Fin (r + d)) A := Matrix.zeroExtend h X
  let a : Fin r → ℝ≥0 := fun i => ∑ j : Fin r, ‖X i j‖₊
  let b : Fin (r + d) → ℝ≥0 := fun i => ∑ j : Fin (r + d), ‖Z i j‖₊
  have hnew (i : Fin (r + d)) (hi : r ≤ i.val) : b i = 0 := by
    change (∑ j : Fin (r + d), ‖Z i j‖₊) = 0
    apply Finset.sum_eq_zero
    intro j _
    rw [show Z i j = 0 from Matrix.zeroExtend_of_row h X i j hi, nnnorm_zero]
  have hrow (i : Fin r) : b (i.castLE h) = a i := by
    change (∑ j : Fin (r + d), ‖Z (i.castLE h) j‖₊) =
      ∑ j : Fin r, ‖X i j‖₊
    calc
      (∑ j : Fin (r + d), ‖Z (i.castLE h) j‖₊) =
          ∑ j : Fin r, ‖Z (i.castLE h) (Fin.castAdd d j)‖₊ := by
        apply Fin.sum_trunc
        intro j
        have hj : r ≤ (Fin.natAdd r j).val := by
          exact Nat.le_add_right r j.val
        rw [show Z (i.castLE h) (Fin.natAdd r j) = 0 from
          Matrix.zeroExtend_of_col h X (i.castLE h) (Fin.natAdd r j) hj,
          nnnorm_zero]
      _ = ∑ j : Fin r, ‖X i j‖₊ := by
        apply Finset.sum_congr rfl
        intro j _
        have hj : Fin.castAdd d j = j.castLE h := Fin.ext rfl
        rw [hj, show Z (i.castLE h) (j.castLE h) = X i j from
          Matrix.zeroExtend_castLE h X i j]
  have hsup : (Finset.univ : Finset (Fin (r + d))).sup b =
      (Finset.univ : Finset (Fin r)).sup a := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i _
      by_cases hi : i.val < r
      · let i0 : Fin r := ⟨i.val, hi⟩
        have hi0 : i0.castLE h = i := Fin.ext rfl
        rw [← hi0, hrow]
        exact Finset.le_sup (f := a) (Finset.mem_univ i0)
      · rw [hnew i (Nat.le_of_not_gt hi)]
        exact bot_le
    · apply Finset.sup_le
      intro i _
      rw [← hrow i]
      exact Finset.le_sup (f := b) (Finset.mem_univ (i.castLE h))
  change ‖Z‖ = ‖X‖
  calc
    ‖Z‖ = (((Finset.univ : Finset (Fin (r + d))).sup b : ℝ≥0) : ℝ) :=
      Matrix.linfty_opNorm_def Z
    _ = (((Finset.univ : Finset (Fin r)).sup a : ℝ≥0) : ℝ) :=
      congrArg (fun x : ℝ≥0 => (x : ℝ)) hsup
    _ = ‖X‖ := (Matrix.linfty_opNorm_def X).symm

end Matrix
