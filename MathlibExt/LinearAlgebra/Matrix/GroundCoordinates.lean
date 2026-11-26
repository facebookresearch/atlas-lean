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

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Star.Real

/-!
# Ground-coordinate restriction and zero insertion

Let V be a finite index type and r∈V. The grounding map C_r deletes coordinate r, and J_r
reinserts it as zero: (J_r z)(r)=0 and (J_r z)(v)=z(v) for v≠r. For any real V×V matrix A and
z∈ℝ^(V∖{r}), (J_r z)ᵀA(J_r z)=zᵀ A_(V∖{r},V∖{r}) z. This includes an empty remaining
coordinate set.

Source: Spielman and Teng, arXiv cs/0607105v5, §3.2.
-/

@[expose] public section

noncomputable section

open Finset Matrix
open scoped BigOperators Classical

namespace Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Matrix deleting a root coordinate.**

Let V be a finite index type and r∈V. The grounding map C_r deletes coordinate r, and J_r
reinserts it as zero: (J_r z)(r)=0 and (J_r z)(v)=z(v) for v≠r. The matrix groundRestriction r
represents C_r:x↦x|_(V∖{r}) and consists of the corresponding rows of the identity matrix.
-/
def groundRestriction (r : V) : Matrix {v : V // v ≠ r} V ℝ :=
  (1 : Matrix V V ℝ).submatrix Subtype.val id

/-- **Matrix reinserting a zero root coordinate.**

Let V be a finite index type and r∈V. The grounding map C_r deletes coordinate r, and J_r
reinserts it as zero: (J_r z)(r)=0 and (J_r z)(v)=z(v) for v≠r. The matrix zeroInsertion r is
J_r=C_rᵀ, with entry 1 on matching nonroot coordinates and zero elsewhere.
-/
def zeroInsertion (r : V) : Matrix V {v : V // v ≠ r} ℝ := (groundRestriction r)ᵀ

theorem groundRestriction_mulVec (r : V) (x : V → ℝ) :
    groundRestriction r *ᵥ x = x ∘ Subtype.val := by
  ext v
  simp [groundRestriction, Matrix.mulVec, dotProduct, Matrix.one_apply]

omit [Fintype V] in
theorem zeroInsertion_eq_submatrix_one (r : V) :
    zeroInsertion r = (1 : Matrix V V ℝ).submatrix id Subtype.val := by
  rw [zeroInsertion, groundRestriction, transpose_submatrix, transpose_one]

theorem zeroInsertion_mulVec_apply (r : V) (z : {v : V // v ≠ r} → ℝ) (v : V) :
    (zeroInsertion r *ᵥ z) v = if hv : v = r then 0 else z ⟨v, hv⟩ := by
  rw [zeroInsertion_eq_submatrix_one]
  by_cases hv : v = r
  · subst v
    simp only [Matrix.mulVec, dotProduct, submatrix_apply]
    apply Finset.sum_eq_zero
    intro i _
    simp [Ne.symm i.property]
  · rw [dite_eq_right hv]
    have hi (i : {v : V // v ≠ r}) : (v = i.val) ↔ i = ⟨v, hv⟩ :=
      ⟨fun h => Subtype.ext h.symm, fun h => (congrArg Subtype.val h).symm⟩
    simp only [Matrix.mulVec, dotProduct, submatrix_apply, id_eq, Matrix.one_apply]
    simp_rw [hi]
    simp

@[simp]
theorem zeroInsertion_mulVec_root (r : V) (z : {v : V // v ≠ r} → ℝ) :
    (zeroInsertion r *ᵥ z) r = 0 := by
  simp [zeroInsertion_mulVec_apply]

@[simp]
theorem groundRestriction_mul_zeroInsertion (r : V) :
    groundRestriction r * zeroInsertion r = 1 := by
  have h := one_submatrix_mul (Subtype.val : {v : V // v ≠ r} → V)
    (Equiv.refl V) (zeroInsertion r)
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp] at h
  rw [groundRestriction, h]
  ext i j
  simp [zeroInsertion_eq_submatrix_one, Matrix.one_apply, Subtype.val_injective.eq_iff]

theorem groundRestriction_zeroInsertion_mulVec (r : V) (z : {v : V // v ≠ r} → ℝ) :
    groundRestriction r *ᵥ (zeroInsertion r *ᵥ z) = z := by
  rw [mulVec_mulVec, groundRestriction_mul_zeroInsertion, one_mulVec]

theorem groundRestriction_mul_mul_zeroInsertion (r : V) (A : Matrix V V ℝ) :
    groundRestriction r * A * zeroInsertion r = A.submatrix Subtype.val Subtype.val := by
  have h := one_submatrix_mul (Subtype.val : {v : V // v ≠ r} → V) (Equiv.refl V) A
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp] at h
  rw [groundRestriction, h, zeroInsertion_eq_submatrix_one]
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp,
    submatrix_submatrix, Function.comp_id] using
      mul_submatrix_one (Equiv.refl V) (Subtype.val : {v : V // v ≠ r} → V)
        (A.submatrix Subtype.val id)

/-- **Quadratic energy of the grounded principal submatrix.**

Let V be a finite index type and r∈V. The grounding map C_r deletes coordinate r, and J_r
reinserts it as zero: (J_r z)(r)=0 and (J_r z)(v)=z(v) for v≠r. For arbitrary A:Matrix V V ℝ
and z∈ℝ^(V∖{r}), (J_r z)ᵀA(J_r z)=zᵀ(A.submatrix Subtype.val Subtype.val)z.
-/
theorem zeroInsertion_energy (r : V) (A : Matrix V V ℝ)
    (z : {v : V // v ≠ r} → ℝ) :
    (zeroInsertion r *ᵥ z) ⬝ᵥ (A *ᵥ (zeroInsertion r *ᵥ z)) =
      z ⬝ᵥ (A.submatrix Subtype.val Subtype.val *ᵥ z) := by
  calc
    (zeroInsertion r *ᵥ z) ⬝ᵥ (A *ᵥ (zeroInsertion r *ᵥ z)) =
        z ⬝ᵥ (groundRestriction r *ᵥ (A *ᵥ (zeroInsertion r *ᵥ z))) :=
      (dotProduct_comm _ _).trans
        (dotProduct_transpose_mulVec (groundRestriction r) (A *ᵥ (zeroInsertion r *ᵥ z)) z)
    _ = z ⬝ᵥ (A.submatrix Subtype.val Subtype.val *ᵥ z) := by
      rw [mulVec_mulVec, mulVec_mulVec, groundRestriction_mul_mul_zeroInsertion]

theorem eq_of_groundRestriction_eq_sum_eq (r : V) {x y : V → ℝ}
    (hxy : groundRestriction r *ᵥ x = groundRestriction r *ᵥ y)
    (hs : ∑ v, x v = ∑ v, y v) : x = y := by
  have hrest (v : V) (hv : v ≠ r) : x v = y v := by
    have h := congrArg (fun z : {v : V // v ≠ r} → ℝ => z ⟨v, hv⟩) hxy
    simpa only [groundRestriction_mulVec, Function.comp_apply] using h
  have hz : ∑ v, (x v - y v) = 0 := by rw [sum_sub_distrib, hs, sub_self]
  have hsingle : ∑ v, (x v - y v) = x r - y r := by
    apply Finset.sum_eq_single r
    · intro v _ hv
      rw [hrest v hv, sub_self]
    · simp
  have hr : x r = y r := sub_eq_zero.mp (hsingle.symm.trans hz)
  ext v
  by_cases hv : v = r
  · simpa only [hv] using hr
  · exact hrest v hv

end Matrix
