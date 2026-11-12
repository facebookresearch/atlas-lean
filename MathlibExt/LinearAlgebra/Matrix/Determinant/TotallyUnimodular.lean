/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Integral solutions of totally unimodular systems

A nonsingular totally unimodular real matrix with integer right-hand side
has only integral solutions. Rectangular bases are covered by applying
`Matrix.IsTotallyUnimodular.submatrix` first.
-/

public section

namespace Matrix

/-- Every solution of a nonsingular totally unimodular real system with
integer right-hand side is an integer vector. Dimensions may be zero. -/
theorem IsTotallyUnimodular.exists_int_vec {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsTotallyUnimodular)
    (hdet : A.det ≠ 0) (b : Fin n → ℤ) {x : Fin n → ℝ}
    (hAx : A *ᵥ x = fun i => (b i : ℝ)) :
    ∃ z : Fin n → ℤ, ∀ i, (z i : ℝ) = x i := by
  classical
  have hentries : ∀ i j, ∃ z : ℤ, (z : ℝ) = A i j := by
    intro i j
    obtain ⟨s, hs⟩ := hA.apply i j
    exact ⟨s, (SignType.intCast_cast s).trans hs⟩
  choose entries hentries using hentries
  let M : Matrix (Fin n) (Fin n) ℤ := Matrix.of entries
  have hM (i j : Fin n) : (M i j : ℝ) = A i j := hentries i j
  have hcramer (i : Fin n) :
      ((updateCol M i b).det : ℝ) = A.cramer (fun j => (b j : ℝ)) i := by
    rw [Int.cast_det, cramer_apply]
    congr 1
    ext j k
    simp only [map_apply, updateCol_apply]
    split_ifs
    · rfl
    · exact hM j k
  have hsol : A.cramer (fun i => (b i : ℝ)) = A.det • x := by
    rw [← hAx, cramer_eq_adjugate_mulVec, mulVec_mulVec,
      adjugate_mul, smul_mulVec, one_mulVec]
  obtain ⟨s, hs⟩ := (isTotallyUnimodular_iff A).mp hA n id id
  simp only [submatrix_id_id] at hs
  cases s with
  | zero => exact (hdet hs.symm).elim
  | neg =>
    refine ⟨fun i => -(updateCol M i b).det, fun i => ?_⟩
    rw [Int.cast_neg, hcramer, hsol, ← hs]
    simp
  | pos =>
    refine ⟨fun i => (updateCol M i b).det, fun i => ?_⟩
    rw [hcramer, hsol, ← hs]
    simp

end Matrix
