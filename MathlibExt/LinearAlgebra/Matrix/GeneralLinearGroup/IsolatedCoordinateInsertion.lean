/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.MonomialCoordinateInsertion

/-!
# Insertion of an isolated matrix coordinate

A unit at a chosen coordinate and an invertible matrix on its complement define
a block insertion into the general linear group. The construction is compatible
with monomial matrices and coefficient maps.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open PermutationBilinearCocycle
open Matrix

universe uι uR vR wR

/-- Deleted indices distinct from `c`, short alias. -/
abbrev Del (ι : Type uι) (c : ι) := DeletedIndex ι c

/-- Square matrices on `ι`, short alias. -/
abbrev Mat (ι : Type uι) (R : Type uR) := Matrix ι ι R

/-- Square matrices on `DeletedIndex ι c`, short alias. -/
abbrev DelMat (ι : Type uι) (c : ι) (R : Type uR) :=
  Matrix (Del ι c) (Del ι c) R

section InsertionSemiring

variable {ι : Type uι} [DecidableEq ι] [Fintype ι] {R : Type uR} [Semiring R] (c : ι)


/-- Matrix with pivot `a` at `(c,c)` and `x` on the complementary principal block. -/
def insertVal (a : Rˣ) (x : GL (Del ι c) R) : Mat ι R :=
  fun i j =>
    if hi : i = c then
      if j = c then (a : R) else 0
    else
      if hj : j = c then 0
      else (x.val : DelMat ι c R) (⟨i, hi⟩ : Del ι c) (⟨j, hj⟩ : Del ι c)

/-- Inverse matrix for the block insertion: `a⁻¹` at `(c,c)` and `x⁻¹` on complement. -/
def insertInvVal (a : Rˣ) (x : GL (Del ι c) R) : Mat ι R :=
  fun i j =>
    if hi : i = c then
      if j = c then ((a⁻¹ : Rˣ) : R) else 0
    else
      if hj : j = c then 0
      else ((x⁻¹).val : DelMat ι c R) (⟨i, hi⟩ : Del ι c) (⟨j, hj⟩ : Del ι c)

omit [Fintype ι] in
lemma one_submatrix (i j : ι) (hi : i ≠ c) (hj : j ≠ c) :
    (1 : Mat ι R) i j =
      (1 : DelMat ι c R) (⟨i, hi⟩ : Del ι c) (⟨j, hj⟩ : Del ι c) := by
  simp only [Matrix.one_apply]
  by_cases hij : i = j
  · have hij' : (⟨i, hi⟩ : Del ι c) = (⟨j, hj⟩ : Del ι c) := Subtype.ext hij
    simp [hij]
  · have hij' : (⟨i, hi⟩ : Del ι c) ≠ (⟨j, hj⟩ : Del ι c) := by
      intro h
      apply hij
      exact congrArg Subtype.val h
    simp [hij, hij']

lemma val_mul_inv_aux (a : Rˣ) (x : GL (Del ι c) R) :
    insertVal c a x * insertInvVal c a x = 1 := by
  ext i j
  classical
  simp only [Matrix.mul_apply]
  by_cases hi : i = c
  · by_cases hj : j = c
    · rw [hi, hj]
      have h_zero : ∀ k : ι, k ≠ c → insertVal c a x c k * insertInvVal c a x k c = 0 := by
        intro k hk
        have : insertVal c a x c k = 0 := by unfold insertVal; simp [hk]
        rw [this, zero_mul]
      have h_sum : ∑ k : ι, insertVal c a x c k * insertInvVal c a x k c =
          insertVal c a x c c * insertInvVal c a x c c :=
        Fintype.sum_eq_single c (fun b hb => h_zero b hb)
      rw [h_sum]
      have h1 : insertVal c a x c c = (a : R) := by unfold insertVal; simp
      have h2 : insertInvVal c a x c c = ((a⁻¹ : Rˣ) : R) := by unfold insertInvVal; simp
      rw [h1, h2]
      have : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by
        calc (a : R) * ((a⁻¹ : Rˣ) : R)
            = ((a * a⁻¹ : Rˣ) : R) := by rfl
          _ = ((1 : Rˣ) : R) := by rw [mul_inv_cancel]
          _ = 1 := by simp
      rw [this]
      simp
    · have hj' : j ≠ c := hj
      have h_all : ∀ k : ι, insertVal c a x c k * insertInvVal c a x k j = 0 := by
        intro k
        by_cases hk : k = c
        · rw [hk]
          have : insertInvVal c a x c j = 0 := by unfold insertInvVal; simp [hj']
          simp [this]
        · have : insertVal c a x c k = 0 := by unfold insertVal; simp [hk]
          rw [this, zero_mul]
      have h_sum : ∑ k : ι, insertVal c a x c k * insertInvVal c a x k j = 0 :=
        Fintype.sum_eq_zero _ (fun k => h_all k)
      have h_one : (1 : Mat ι R) c j = 0 := by
        rw [Matrix.one_apply, ite_eq_right (Ne.symm hj')]
      rw [hi, h_sum, h_one]
  · by_cases hj : j = c
    · have hi' : i ≠ c := hi
      have h_all : ∀ k : ι, insertVal c a x i k * insertInvVal c a x k c = 0 := by
        intro k
        by_cases hk : k = c
        · rw [hk]
          have : insertVal c a x i c = 0 := by unfold insertVal; simp [hi']
          rw [this, zero_mul]
        · have : insertInvVal c a x k c = 0 := by unfold insertInvVal; simp [hk]
          rw [this, mul_zero]
      have h_sum : ∑ k : ι, insertVal c a x i k * insertInvVal c a x k c = 0 :=
        Fintype.sum_eq_zero _ (fun k => h_all k)
      have h_one : (1 : Mat ι R) i c = 0 := by
        rw [Matrix.one_apply, ite_eq_right hi]
      rw [hj, h_sum, h_one]
    · have hi' : i ≠ c := hi
      have hj' : j ≠ c := hj
      let f : ι → R := fun k => insertVal c a x i k * insertInvVal c a x k j
      have hf_c : f c = 0 := by
        dsimp [f]
        have : insertVal c a x i c = 0 := by unfold insertVal; simp [hi']
        rw [this, zero_mul]
      have h_sum_eq : (∑ k : ι, f k) = ∑ d : Del ι c, f d.1 := by
        have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := c)
        rw [hf_c, zero_add] at h
        exact h
      have h_f_eq : ∀ d : Del ι c,
          f d.1 =
            (x.val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) d *
            ((x⁻¹).val : DelMat ι c R) d (⟨j, hj'⟩ : Del ι c) := by
        intro d
        dsimp [f]
        have hd : d.1 ≠ c := d.property
        have h1 : insertVal c a x i d.1 =
            (x.val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) d := by
          unfold insertVal; simp [hi', hd]
        have h2 : insertInvVal c a x d.1 j =
            ((x⁻¹).val : DelMat ι c R) d (⟨j, hj'⟩ : Del ι c) := by
          unfold insertInvVal; simp [hd, hj']
        rw [h1, h2]
      have h_sum_sub : (∑ d : Del ι c, f d.1) =
          (x.val * (x⁻¹).val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro d _
        rw [h_f_eq d]
      have h_val_inv : (x.val : Matrix _ _ _) * ((x⁻¹).val : Matrix _ _ _) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc (∑ k : ι, f k) = ∑ d : Del ι c, f d.1 := h_sum_eq
        _ = (x.val * (x⁻¹).val : DelMat ι c R)
            (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := h_sum_sub
        _ = (1 : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := by rw [h_val_inv]
        _ = (1 : Mat ι R) i j := (one_submatrix c i j hi' hj').symm


lemma inv_mul_val_aux (a : Rˣ) (x : GL (Del ι c) R) :
    insertInvVal c a x * insertVal c a x = 1 := by
  ext i j
  classical
  simp only [Matrix.mul_apply]
  by_cases hi : i = c
  · by_cases hj : j = c
    · rw [hi, hj]
      have h_zero : ∀ k : ι, k ≠ c → insertInvVal c a x c k * insertVal c a x k c = 0 := by
        intro k hk
        have : insertInvVal c a x c k = 0 := by unfold insertInvVal; simp [hk]
        rw [this, zero_mul]
      have h_sum : ∑ k : ι, insertInvVal c a x c k * insertVal c a x k c =
          insertInvVal c a x c c * insertVal c a x c c :=
        Fintype.sum_eq_single c (fun b hb => h_zero b hb)
      rw [h_sum]
      have h1 : insertInvVal c a x c c = ((a⁻¹ : Rˣ) : R) := by unfold insertInvVal; simp
      have h2 : insertVal c a x c c = (a : R) := by unfold insertVal; simp
      rw [h1, h2]
      have : ((a⁻¹ : Rˣ) : R) * (a : R) = 1 := by
        calc ((a⁻¹ : Rˣ) : R) * (a : R)
            = ((a⁻¹ * a : Rˣ) : R) := by rfl
          _ = ((1 : Rˣ) : R) := by rw [inv_mul_cancel]
          _ = 1 := by simp
      rw [this]
      simp
    · have hj' : j ≠ c := hj
      have h_all : ∀ k : ι, insertInvVal c a x c k * insertVal c a x k j = 0 := by
        intro k
        by_cases hk : k = c
        · rw [hk]
          have : insertVal c a x c j = 0 := by unfold insertVal; simp [hj']
          simp [this]
        · have : insertInvVal c a x c k = 0 := by unfold insertInvVal; simp [hk]
          rw [this, zero_mul]
      have h_sum : ∑ k : ι, insertInvVal c a x c k * insertVal c a x k j = 0 :=
        Fintype.sum_eq_zero _ (fun k => h_all k)
      have h_one : (1 : Mat ι R) c j = 0 := by
        rw [Matrix.one_apply, ite_eq_right (Ne.symm hj')]
      rw [hi, h_sum, h_one]
  · by_cases hj : j = c
    · have hi' : i ≠ c := hi
      have h_all : ∀ k : ι, insertInvVal c a x i k * insertVal c a x k c = 0 := by
        intro k
        by_cases hk : k = c
        · rw [hk]
          have : insertInvVal c a x i c = 0 := by unfold insertInvVal; simp [hi']
          rw [this, zero_mul]
        · have : insertVal c a x k c = 0 := by unfold insertVal; simp [hk]
          rw [this, mul_zero]
      have h_sum : ∑ k : ι, insertInvVal c a x i k * insertVal c a x k c = 0 :=
        Fintype.sum_eq_zero _ (fun k => h_all k)
      have h_one : (1 : Mat ι R) i c = 0 := by
        rw [Matrix.one_apply, ite_eq_right hi]
      rw [hj, h_sum, h_one]
    · have hi' : i ≠ c := hi
      have hj' : j ≠ c := hj
      let f : ι → R := fun k => insertInvVal c a x i k * insertVal c a x k j
      have hf_c : f c = 0 := by
        dsimp [f]
        have : insertInvVal c a x i c = 0 := by unfold insertInvVal; simp [hi']
        rw [this, zero_mul]
      have h_sum_eq : (∑ k : ι, f k) = ∑ d : Del ι c, f d.1 := by
        have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := c)
        rw [hf_c, zero_add] at h
        exact h
      have h_f_eq : ∀ d : Del ι c,
          f d.1 =
            ((x⁻¹).val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) d *
            (x.val : DelMat ι c R) d (⟨j, hj'⟩ : Del ι c) := by
        intro d
        dsimp [f]
        have hd : d.1 ≠ c := d.property
        have h1 : insertInvVal c a x i d.1 =
            ((x⁻¹).val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) d := by
          unfold insertInvVal; simp [hi', hd]
        have h2 : insertVal c a x d.1 j =
            (x.val : DelMat ι c R) d (⟨j, hj'⟩ : Del ι c) := by
          unfold insertVal; simp [hd, hj']
        rw [h1, h2]
      have h_sum_sub : (∑ d : Del ι c, f d.1) =
          ((x⁻¹).val * x.val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro d _
        rw [h_f_eq d]
      have h_inv_val : ((x⁻¹).val : Matrix _ _ _) * (x.val : Matrix _ _ _) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc (∑ k : ι, f k) = ∑ d : Del ι c, f d.1 := h_sum_eq
        _ = ((x⁻¹).val * x.val : DelMat ι c R)
            (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := h_sum_sub
        _ = (1 : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := by rw [h_inv_val]
        _ = (1 : Mat ι R) i j := (one_submatrix c i j hi' hj').symm


/-- Block-diagonal insertion of a pivot unit and a complementary `GL` element. -/
def insertCoordinateUnit (a : Rˣ) (x : GL (Del ι c) R) : GL ι R where
  val := insertVal c a x
  inv := insertInvVal c a x
  val_inv := val_mul_inv_aux c a x
  inv_val := inv_mul_val_aux c a x

@[simp]
theorem coe_insertCoordinateUnit (a : Rˣ) (x : GL (Del ι c) R) :
    (↑(insertCoordinateUnit c a x) : Mat ι R) = insertVal c a x := rfl

@[simp]
theorem coe_inv_insertCoordinateUnit (a : Rˣ) (x : GL (Del ι c) R) :
    (↑(insertCoordinateUnit c a x)⁻¹ : Mat ι R) = insertInvVal c a x := rfl

theorem coe_insertCoordinateUnit_apply (a : Rˣ) (x : GL (Del ι c) R) (i j : ι) :
    (↑(insertCoordinateUnit c a x) : Mat ι R) i j =
      if hi : i = c then if j = c then (a : R) else 0
      else if hj : j = c then 0
        else (x.val : DelMat ι c R) (⟨i, hi⟩ : Del ι c) (⟨j, hj⟩ : Del ι c) := rfl

theorem coe_inv_insertCoordinateUnit_apply (a : Rˣ) (x : GL (Del ι c) R) (i j : ι) :
    (↑(insertCoordinateUnit c a x)⁻¹ : Mat ι R) i j =
      if hi : i = c then if j = c then ((a⁻¹ : Rˣ) : R) else 0
      else if hj : j = c then 0
        else ((x⁻¹).val : DelMat ι c R) (⟨i, hi⟩ : Del ι c) (⟨j, hj⟩ : Del ι c) := rfl

@[simp]
theorem coe_insertCoordinateUnit_c_c (a : Rˣ) (x : GL (Del ι c) R) :
    (↑(insertCoordinateUnit c a x) : Mat ι R) c c = (a : R) := by
  simp [coe_insertCoordinateUnit, insertVal]

@[simp]
theorem coe_insertCoordinateUnit_c_ne (a : Rˣ) (x : GL (Del ι c) R) {j : ι}
    (hj : j ≠ c) :
    (↑(insertCoordinateUnit c a x) : Mat ι R) c j = 0 := by
  simp [coe_insertCoordinateUnit, insertVal, hj]

@[simp]
theorem coe_insertCoordinateUnit_ne_c (a : Rˣ) (x : GL (Del ι c) R) {i : ι}
    (hi : i ≠ c) :
    (↑(insertCoordinateUnit c a x) : Mat ι R) i c = 0 := by
  simp [coe_insertCoordinateUnit, insertVal, hi]

theorem coe_insertCoordinateUnit_ne_ne (a : Rˣ) (x : GL (Del ι c) R) {i j : ι}
    (hi : i ≠ c) (hj : j ≠ c) :
    (↑(insertCoordinateUnit c a x) : Mat ι R) i j =
      (x.val : DelMat ι c R) (⟨i, hi⟩ : Del ι c) (⟨j, hj⟩ : Del ι c) := by
  simp [coe_insertCoordinateUnit, insertVal, hi, hj]

@[simp]
theorem coe_inv_insertCoordinateUnit_c_c (a : Rˣ) (x : GL (Del ι c) R) :
    (↑(insertCoordinateUnit c a x)⁻¹ : Mat ι R) c c = ((a⁻¹ : Rˣ) : R) := by
  simp [coe_inv_insertCoordinateUnit, insertInvVal]

@[simp]
theorem coe_inv_insertCoordinateUnit_c_ne (a : Rˣ) (x : GL (Del ι c) R) {j : ι}
    (hj : j ≠ c) :
    (↑(insertCoordinateUnit c a x)⁻¹ : Mat ι R) c j = 0 := by
  simp [coe_inv_insertCoordinateUnit, insertInvVal, hj]

@[simp]
theorem coe_inv_insertCoordinateUnit_ne_c (a : Rˣ) (x : GL (Del ι c) R) {i : ι}
    (hi : i ≠ c) :
    (↑(insertCoordinateUnit c a x)⁻¹ : Mat ι R) i c = 0 := by
  simp [coe_inv_insertCoordinateUnit, insertInvVal, hi]

theorem coe_inv_insertCoordinateUnit_ne_ne (a : Rˣ) (x : GL (Del ι c) R) {i j : ι}
    (hi : i ≠ c) (hj : j ≠ c) :
    (↑(insertCoordinateUnit c a x)⁻¹ : Mat ι R) i j =
      ((x⁻¹).val : DelMat ι c R) (⟨i, hi⟩ : Del ι c) (⟨j, hj⟩ : Del ι c) := by
  simp [coe_inv_insertCoordinateUnit, insertInvVal, hi, hj]

theorem insertCoordinateUnit_mul (a₁ a₂ : Rˣ) (x₁ x₂ : GL (Del ι c) R) :
    insertCoordinateUnit c (a₁ * a₂) (x₁ * x₂) =
      insertCoordinateUnit c a₁ x₁ * insertCoordinateUnit c a₂ x₂ := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, coe_insertCoordinateUnit]
  by_cases hi : i = c
  · by_cases hj : j = c
    · rw [hi, hj]
      have h_zero : ∀ k : ι, k ≠ c →
          insertVal c a₁ x₁ c k * insertVal c a₂ x₂ k c = 0 := by
        intro k hk
        have : insertVal c a₁ x₁ c k = 0 := by unfold insertVal; simp [hk]
        rw [this, zero_mul]
      have h_sum : ∑ k : ι, insertVal c a₁ x₁ c k * insertVal c a₂ x₂ k c =
          insertVal c a₁ x₁ c c * insertVal c a₂ x₂ c c :=
        Fintype.sum_eq_single c (fun b hb => h_zero b hb)
      rw [h_sum]
      simp [insertVal, Units.val_mul]
    · have hj' : j ≠ c := hj
      have h_all : ∀ k : ι, insertVal c a₁ x₁ c k * insertVal c a₂ x₂ k j = 0 := by
        intro k
        by_cases hk : k = c
        · rw [hk]
          have : insertVal c a₂ x₂ c j = 0 := by unfold insertVal; simp [hj']
          simp [this]
        · have : insertVal c a₁ x₁ c k = 0 := by unfold insertVal; simp [hk]
          rw [this, zero_mul]
      have h_sum : ∑ k : ι, insertVal c a₁ x₁ c k * insertVal c a₂ x₂ k j = 0 :=
        Fintype.sum_eq_zero _ (fun k => h_all k)
      rw [hi, h_sum]
      have : insertVal c (a₁ * a₂) (x₁ * x₂) c j = 0 := by unfold insertVal; simp [hj']
      rw [this]
  · by_cases hj : j = c
    · have hi' : i ≠ c := hi
      have h_all : ∀ k : ι, insertVal c a₁ x₁ i k * insertVal c a₂ x₂ k c = 0 := by
        intro k
        by_cases hk : k = c
        · rw [hk]
          have : insertVal c a₁ x₁ i c = 0 := by unfold insertVal; simp [hi']
          rw [this, zero_mul]
        · have : insertVal c a₂ x₂ k c = 0 := by unfold insertVal; simp [hk]
          rw [this, mul_zero]
      have h_sum : ∑ k : ι, insertVal c a₁ x₁ i k * insertVal c a₂ x₂ k c = 0 :=
        Fintype.sum_eq_zero _ (fun k => h_all k)
      rw [hj, h_sum]
      have : insertVal c (a₁ * a₂) (x₁ * x₂) i c = 0 := by unfold insertVal; simp [hi']
      rw [this]
    · have hi' : i ≠ c := hi
      have hj' : j ≠ c := hj
      let f : ι → R := fun k => insertVal c a₁ x₁ i k * insertVal c a₂ x₂ k j
      have hf_c : f c = 0 := by
        dsimp [f]
        have : insertVal c a₁ x₁ i c = 0 := by unfold insertVal; simp [hi']
        rw [this, zero_mul]
      have h_sum_eq : (∑ k : ι, f k) = ∑ d : Del ι c, f d.1 := by
        have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := c)
        rw [hf_c, zero_add] at h
        exact h
      have h_f_eq : ∀ d : Del ι c,
          f d.1 =
            (x₁.val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) d *
            (x₂.val : DelMat ι c R) d (⟨j, hj'⟩ : Del ι c) := by
        intro d
        dsimp [f]
        have hd : d.1 ≠ c := d.property
        have h1 : insertVal c a₁ x₁ i d.1 =
            (x₁.val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) d := by
          unfold insertVal; simp [hi', hd]
        have h2 : insertVal c a₂ x₂ d.1 j =
            (x₂.val : DelMat ι c R) d (⟨j, hj'⟩ : Del ι c) := by
          unfold insertVal; simp [hd, hj']
        rw [h1, h2]
      have h_sum_sub : (∑ d : Del ι c, f d.1) =
          ((x₁.val : DelMat ι c R) *
            (x₂.val : DelMat ι c R)) (⟨i, hi'⟩ : Del ι c)
            (⟨j, hj'⟩ : Del ι c) := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro d _
        rw [h_f_eq d]
      have h_mul : ((x₁ * x₂).val : DelMat ι c R) =
          (x₁.val : DelMat ι c R) * (x₂.val : DelMat ι c R) := by
        rw [← Units.val_mul]
      have h_eq : (∑ k : ι, f k) =
          ((x₁ * x₂).val : DelMat ι c R)
            (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := by
        calc (∑ k : ι, f k) = ∑ d : Del ι c, f d.1 := h_sum_eq
          _ = ((x₁.val : DelMat ι c R) *
              (x₂.val : DelMat ι c R)) (⟨i, hi'⟩ : Del ι c)
              (⟨j, hj'⟩ : Del ι c) := h_sum_sub
          _ = ((x₁ * x₂).val : DelMat ι c R)
              (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := by
            rw [h_mul]
      have h_left : insertVal c (a₁ * a₂) (x₁ * x₂) i j =
          ((x₁ * x₂).val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := by
        unfold insertVal; simp [hi', hj']
      calc insertVal c (a₁ * a₂) (x₁ * x₂) i j
          = ((x₁ * x₂).val : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := h_left
        _ = (∑ k : ι, f k) := h_eq.symm
        _ = ∑ j_1, insertVal c a₁ x₁ i j_1 * insertVal c a₂ x₂ j_1 j := rfl

theorem insertCoordinateUnit_one :
    insertCoordinateUnit c (1 : Rˣ) (1 : GL (Del ι c) R) = 1 := by
  apply Units.ext
  ext i j
  simp only [Units.val_one, coe_insertCoordinateUnit]
  by_cases hi : i = c
  · by_cases hj : j = c
    · rw [hi, hj]
      simp [insertVal]
    · have hj' : j ≠ c := hj
      have h1 : insertVal c (1 : Rˣ) (1 : GL _ R) c j = 0 := by unfold insertVal; simp [hj']
      have h_one : (1 : Mat ι R) c j = 0 := by
        rw [Matrix.one_apply, ite_eq_right (Ne.symm hj')]
      rw [hi, h1, h_one]
  · by_cases hj : j = c
    · have hi' : i ≠ c := hi
      have h1 : insertVal c (1 : Rˣ) (1 : GL _ R) i c = 0 := by unfold insertVal; simp [hi']
      have h_one : (1 : Mat ι R) i c = 0 := by
        rw [Matrix.one_apply, ite_eq_right hi]
      rw [hj, h1, h_one]
    · have hi' : i ≠ c := hi
      have hj' : j ≠ c := hj
      have h1 : insertVal c (1 : Rˣ) (1 : GL _ R) i j =
          (1 : DelMat ι c R) (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) := by
        unfold insertVal
        simp [hi', hj', Units.val_one]
      rw [h1]
      simp only [Matrix.one_apply]
      by_cases hij : i = j
      · have : (⟨i, hi'⟩ : Del ι c) = (⟨j, hj'⟩ : Del ι c) := Subtype.ext hij
        simp [hij]
      · have : (⟨i, hi'⟩ : Del ι c) ≠ (⟨j, hj'⟩ : Del ι c) := by
          intro h
          apply hij
          exact congrArg Subtype.val h
        simp [hij]

/-- Bundled monoid hom `Rˣ × GL (DeletedIndex) →* GL ι`. -/
def insertCoordinateUnitHom : Rˣ × GL (Del ι c) R →* GL ι R where
  toFun p := insertCoordinateUnit c p.1 p.2
  map_one' := insertCoordinateUnit_one c
  map_mul' := by
    intro p q
    rcases p with ⟨a₁, x₁⟩
    rcases q with ⟨a₂, x₂⟩
    simp only [Prod.mul_def]
    rw [insertCoordinateUnit_mul]

theorem insertCoordinateUnitHom_apply (a : Rˣ) (x : GL (Del ι c) R) :
    insertCoordinateUnitHom c (a, x) = insertCoordinateUnit c a x := rfl

variable {S : Type vR} [Semiring S] {T : Type wR} [Semiring T]

theorem mapRingHom_insertCoordinateUnit (f : R →+* S)
    (a : Rˣ) (x : GL (Del ι c) R) :
    Matrix.GeneralLinearGroup.mapRingHom f (insertCoordinateUnit c a x) =
      insertCoordinateUnit c (Units.map f a) (Matrix.GeneralLinearGroup.mapRingHom f x) := by
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply, coe_insertCoordinateUnit]
  by_cases hi : i = c
  · by_cases hj : j = c
    · rw [hi, hj]
      simp [insertVal]
    · have hj' : j ≠ c := hj
      rw [hi]
      simp [insertVal, hj', RingHom.map_zero]
  · by_cases hj : j = c
    · have hi' : i ≠ c := hi
      simp [insertVal, hi', hj, RingHom.map_zero]
    · have hi' : i ≠ c := hi
      have hj' : j ≠ c := hj
      simp only [insertVal, dite_eq_right hi', dite_eq_right hj']
      simp [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply]

theorem insertCoordinateUnit_mapRingHom_id (a : Rˣ) (x : GL (Del ι c) R) :
    Matrix.GeneralLinearGroup.mapRingHom (RingHom.id R) (insertCoordinateUnit c a x) =
      insertCoordinateUnit c a x := by
  rw [mapRingHom_insertCoordinateUnit]
  simp

theorem insertCoordinateUnit_mapRingHom_comp (f : R →+* S) (g : S →+* T)
    (a : Rˣ) (x : GL (Del ι c) R) :
    Matrix.GeneralLinearGroup.mapRingHom (g.comp f) (insertCoordinateUnit c a x) =
      Matrix.GeneralLinearGroup.mapRingHom g
        (Matrix.GeneralLinearGroup.mapRingHom f (insertCoordinateUnit c a x)) := by
  have h := Matrix.GeneralLinearGroup.mapRingHom_comp (n := ι) f g
  exact DFunLike.congr_fun h.symm (insertCoordinateUnit c a x)

end InsertionSemiring

section IsolationRing

variable {ι : Type uι} [DecidableEq ι] [Fintype ι] {R : Type uR} [Ring R] (c : ι)

theorem isIsolated_insertCoordinateUnit (a : Rˣ) (x : GL (Del ι c) R) :
    IsolatedCoordinate (insertCoordinateUnit c a x : GL ι R) c where
  col_zero _ hi := coe_insertCoordinateUnit_ne_c c a x hi
  row_zero _ hj := coe_insertCoordinateUnit_c_ne c a x hj

theorem deleteCoordinate_insertCoordinateUnit (a : Rˣ) (x : GL (Del ι c) R)
    (h : IsolatedCoordinate (insertCoordinateUnit c a x : GL ι R) c) :
    deleteCoordinate (insertCoordinateUnit c a x) c h = x := by
  apply Units.ext
  ext i j
  simp only [coe_deleteCoordinate, Matrix.submatrix_apply]
  have hi : i.val ≠ c := i.property
  have hj : j.val ≠ c := j.property
  have h1 : (↑(insertCoordinateUnit c a x) : Mat ι R) i.val j.val =
      (x.val : DelMat ι c R) (⟨i.val, hi⟩ : Del ι c) (⟨j.val, hj⟩ : Del ι c) :=
    coe_insertCoordinateUnit_ne_ne c a x hi hj
  have hi_eq : (⟨i.val, hi⟩ : Del ι c) = i := Subtype.ext rfl
  have hj_eq : (⟨j.val, hj⟩ : Del ι c) = j := Subtype.ext rfl
  rw [h1, hi_eq, hj_eq]

theorem deleteCoordinate_insertCoordinateUnit' (a : Rˣ) (x : GL (Del ι c) R) :
    deleteCoordinate (insertCoordinateUnit c a x) c (isIsolated_insertCoordinateUnit c a x) = x :=
  deleteCoordinate_insertCoordinateUnit c a x _

end IsolationRing

section PivotRing

variable {ι : Type uι} [DecidableEq ι] [Fintype ι] {R : Type uR} [Ring R] (c : ι)

lemma pivot_val_inv_aux (g : GL ι R) (h : IsolatedCoordinate g c) :
    (↑g : Mat ι R) c c * (↑(g⁻¹) : Mat ι R) c c = 1 := by
  classical
  have hmul : (↑g : Mat ι R) * (↑(g⁻¹) : Mat ι R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h_at : ((↑g : Mat ι R) * (↑(g⁻¹) : Mat ι R)) c c = (1 : Mat ι R) c c := by
    rw [hmul]
  simp only [Matrix.mul_apply] at h_at
  have h_one : (1 : Mat ι R) c c = 1 := by simp
  rw [h_one] at h_at
  have h_zero : ∀ k : ι, k ≠ c → (↑g : Mat ι R) c k * (↑(g⁻¹) : Mat ι R) k c = 0 := by
    intro k hk
    rw [h.row_zero k hk, zero_mul]
  have h_sum : ∑ k : ι, (↑g : Mat ι R) c k * (↑(g⁻¹) : Mat ι R) k c =
      (↑g : Mat ι R) c c * (↑(g⁻¹) : Mat ι R) c c :=
    Fintype.sum_eq_single c (fun b hb => h_zero b hb)
  rw [h_sum] at h_at
  exact h_at

lemma pivot_inv_val_aux (g : GL ι R) (h : IsolatedCoordinate g c) :
    (↑(g⁻¹) : Mat ι R) c c * (↑g : Mat ι R) c c = 1 := by
  classical
  have hmul : (↑(g⁻¹) : Mat ι R) * (↑g : Mat ι R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h_at : ((↑(g⁻¹) : Mat ι R) * (↑g : Mat ι R)) c c = (1 : Mat ι R) c c := by
    rw [hmul]
  simp only [Matrix.mul_apply] at h_at
  have h_one : (1 : Mat ι R) c c = 1 := by simp
  rw [h_one] at h_at
  have h_zero : ∀ k : ι, k ≠ c → (↑(g⁻¹) : Mat ι R) c k * (↑g : Mat ι R) k c = 0 := by
    intro k hk
    rw [h.col_zero k hk, mul_zero]
  have h_sum : ∑ k : ι, (↑(g⁻¹) : Mat ι R) c k * (↑g : Mat ι R) k c =
      (↑(g⁻¹) : Mat ι R) c c * (↑g : Mat ι R) c c :=
    Fintype.sum_eq_single c (fun b hb => h_zero b hb)
  rw [h_sum] at h_at
  exact h_at

/-- Pivot unit of an isolated coordinate: `g c c` with inverse `(g⁻¹) c c`. -/
def isolatedPivotUnit (g : GL ι R) (h : IsolatedCoordinate g c) : Rˣ where
  val := (↑g : Mat ι R) c c
  inv := (↑(g⁻¹) : Mat ι R) c c
  val_inv := pivot_val_inv_aux c g h
  inv_val := pivot_inv_val_aux c g h

@[simp]
theorem coe_isolatedPivotUnit (g : GL ι R) (h : IsolatedCoordinate g c) :
    (isolatedPivotUnit c g h : R) = (↑g : Mat ι R) c c := rfl

theorem coe_inv_isolatedPivotUnit (g : GL ι R) (h : IsolatedCoordinate g c) :
    ((isolatedPivotUnit c g h)⁻¹ : Rˣ).val = (↑(g⁻¹) : Mat ι R) c c := rfl

theorem insert_isolatedPivotUnit_deleteCoordinate (g : GL ι R)
    (h : IsolatedCoordinate g c) :
    insertCoordinateUnit c (isolatedPivotUnit c g h) (deleteCoordinate g c h) = g := by
  classical
  apply Units.ext
  ext i j
  by_cases hi : i = c
  · by_cases hj : j = c
    · rw [hi, hj]
      simp [coe_insertCoordinateUnit_c_c]
    · have hj' : j ≠ c := hj
      rw [hi]
      have hl :
          (↑(insertCoordinateUnit c
              (isolatedPivotUnit c g h) (deleteCoordinate g c h)) : Mat ι R) c j = 0 :=
        coe_insertCoordinateUnit_c_ne c _ _ hj'
      rw [hl]
      exact (h.row_zero j hj').symm
  · by_cases hj : j = c
    · have hi' : i ≠ c := hi
      have hl :
          (↑(insertCoordinateUnit c
              (isolatedPivotUnit c g h) (deleteCoordinate g c h)) : Mat ι R) i c = 0 :=
        coe_insertCoordinateUnit_ne_c c _ _ hi'
      rw [hj]
      rw [hl]
      exact (h.col_zero i hi').symm
    · have hi' : i ≠ c := hi
      have hj' : j ≠ c := hj
      calc (↑(insertCoordinateUnit c
            (isolatedPivotUnit c g h) (deleteCoordinate g c h)) : Mat ι R) i j
          = (↑(deleteCoordinate g c h) : Matrix _ _ _) (⟨i, hi'⟩ : Del ι c) (⟨j, hj'⟩ : Del ι c) :=
              coe_insertCoordinateUnit_ne_ne c _ _ hi' hj'
        _ = (↑g : Mat ι R) i j :=
              coe_of_ne_ne g c h hi' hj'

theorem eq_of_pivot_and_delete_eq {g₁ g₂ : GL ι R}
    {h₁ : IsolatedCoordinate g₁ c} {h₂ : IsolatedCoordinate g₂ c}
    (hpivot : (↑g₁ : Mat ι R) c c = (↑g₂ : Mat ι R) c c)
    (hdel : deleteCoordinate g₁ c h₁ = deleteCoordinate g₂ c h₂) :
    g₁ = g₂ := by
  have h1 := insert_isolatedPivotUnit_deleteCoordinate c g₁ h₁
  have h2 := insert_isolatedPivotUnit_deleteCoordinate c g₂ h₂
  have hpivot_units : isolatedPivotUnit c g₁ h₁ = isolatedPivotUnit c g₂ h₂ := by
    apply Units.ext
    exact hpivot
  calc g₁ = insertCoordinateUnit c (isolatedPivotUnit c g₁ h₁) (deleteCoordinate g₁ c h₁) := h1.symm
    _ = insertCoordinateUnit c (isolatedPivotUnit c g₂ h₂) (deleteCoordinate g₂ c h₂) := by
        rw [hpivot_units, hdel]
    _ = g₂ := h2

variable {S : Type vR} [Ring S]

theorem mapRingHom_isolatedPivotUnit (f : R →+* S)
    (g : GL ι R) (h : IsolatedCoordinate g c) :
    Units.map f (isolatedPivotUnit c g h) =
      isolatedPivotUnit c (Matrix.GeneralLinearGroup.mapRingHom f g) (h.map f) := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply]

theorem mapRingHom_reconstruction (f : R →+* S)
    (g : GL ι R) (h : IsolatedCoordinate g c) :
    Matrix.GeneralLinearGroup.mapRingHom f g =
      insertCoordinateUnit c (Units.map f (isolatedPivotUnit c g h))
        (Matrix.GeneralLinearGroup.mapRingHom f (deleteCoordinate g c h)) := by
  have h_recon := insert_isolatedPivotUnit_deleteCoordinate c g h
  calc Matrix.GeneralLinearGroup.mapRingHom f g
      = Matrix.GeneralLinearGroup.mapRingHom f
          (insertCoordinateUnit c (isolatedPivotUnit c g h) (deleteCoordinate g c h)) := by
            rw [h_recon]
    _ = insertCoordinateUnit c (Units.map f (isolatedPivotUnit c g h))
          (Matrix.GeneralLinearGroup.mapRingHom f (deleteCoordinate g c h)) := by
            exact mapRingHom_insertCoordinateUnit c f
              (isolatedPivotUnit c g h) (deleteCoordinate g c h)

end PivotRing

section MonomialBridge

variable {ι : Type uι} [DecidableEq ι] [Fintype ι] {R : Type uR} [Semiring R] (c : ι)

theorem insertCoordinateUnit_monomial (a : Rˣ) (x : MonomialBase Rˣ (Del ι c)) :
    insertCoordinateUnit c a (monomialMatrixHom R (Del ι c) x) =
      monomialMatrixHom R ι (monomialInsert c a x) := by
  classical
  apply Units.ext
  ext i j
  by_cases hi : i = c
  · by_cases hj : j = c
    · rw [hi, hj]
      rw [coe_insertCoordinateUnit_c_c]
      exact (monomialInsert_matrix_c_c c a x).symm
    · have hj' : j ≠ c := hj
      rw [hi]
      have hl : (↑(insertCoordinateUnit c a (monomialMatrixHom R (Del ι c) x)) : Mat ι R) c j = 0 :=
        coe_insertCoordinateUnit_c_ne c a (monomialMatrixHom R (Del ι c) x) hj'
      rw [hl]
      exact (monomialInsert_matrix_row_c c a x hj').symm
  · by_cases hj : j = c
    · have hi' : i ≠ c := hi
      rw [hj]
      have hl : (↑(insertCoordinateUnit c a (monomialMatrixHom R (Del ι c) x)) : Mat ι R) i c = 0 :=
        coe_insertCoordinateUnit_ne_c c a (monomialMatrixHom R (Del ι c) x) hi'
      rw [hl]
      exact (monomialInsert_matrix_col_c c a x hi').symm
    · have hi' : i ≠ c := hi
      have hj' : j ≠ c := hj
      rw [coe_insertCoordinateUnit_ne_ne c a (monomialMatrixHom R (Del ι c) x) hi' hj']
      rw [monomialInsert_matrix_block c a x hi' hj']

variable {S : Type vR} [Semiring S]

theorem insertCoordinateUnit_monomial_naturality (f : R →+* S)
    (a : Rˣ) (x : MonomialBase Rˣ (Del ι c)) :
    Matrix.GeneralLinearGroup.mapRingHom f
        (insertCoordinateUnit c a (monomialMatrixHom R (Del ι c) x)) =
      insertCoordinateUnit c (Units.map f a)
        (monomialMatrixHom S (Del ι c) (monomialBaseHom (Units.map f) x)) := by
  calc Matrix.GeneralLinearGroup.mapRingHom f
        (insertCoordinateUnit c a (monomialMatrixHom R (Del ι c) x))
      = insertCoordinateUnit c (Units.map f a)
          (Matrix.GeneralLinearGroup.mapRingHom f (monomialMatrixHom R (Del ι c) x)) := by
            rw [mapRingHom_insertCoordinateUnit]
    _ = insertCoordinateUnit c (Units.map f a)
          (monomialMatrixHom S (Del ι c) (monomialBaseHom (Units.map f) x)) := by
            rw [monomialMatrixHom_mapRingHom_apply]

end MonomialBridge

end Matrix.GeneralLinearGroup
