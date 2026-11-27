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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.GeneralLinearEquiv
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.IsolatedCoordinate
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.IsolatedCoordinateInsertion
public import Mathlib.Data.Fintype.BigOperators

/-!
# Isolated entries in rectangular matrices
-/

@[expose] public section

namespace Matrix.GeneralLinearEquiv

open Matrix.GeneralLinearGroup

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {R S : Type*} [Semiring R] [Semiring S]

/-! ### Predicate `IsolatedEntry` -/

structure IsolatedEntry (e : GeneralLinearEquiv m n R) (r : m) (c : n) : Prop where
  row_zero : ∀ j : n, j ≠ c → e.val r j = 0
  col_zero : ∀ i : m, i ≠ r → e.val i c = 0

namespace IsolatedEntry

variable {e : GeneralLinearEquiv m n R} {r : m} {c : n}

theorem row_zero_of_ne (h : IsolatedEntry e r c) {j : n} (hj : j ≠ c) :
    e.val r j = 0 :=
  h.row_zero j hj

theorem col_zero_of_ne (h : IsolatedEntry e r c) {i : m} (hi : i ≠ r) :
    e.val i c = 0 :=
  h.col_zero i hi

theorem mk_of_if
    (hrow : ∀ j : n, e.val r j = if j = c then e.val r c else 0)
    (hcol : ∀ i : m, e.val i c = if i = r then e.val r c else 0) :
    IsolatedEntry e r c where
  row_zero j hj := by rw [hrow j, ite_eq_right hj]
  col_zero i hi := by rw [hcol i, ite_eq_right hi]

theorem map (f : R →+* S) (h : IsolatedEntry e r c) :
    IsolatedEntry (e.map f) r c where
  row_zero j hj := by
    have : (e.map f).val r j = f (e.val r j) := by
      simp [val_map, Matrix.map_apply]
    rw [this, h.row_zero j hj, f.map_zero]
  col_zero i hi := by
    have : (e.map f).val i c = f (e.val i c) := by
      simp [val_map, Matrix.map_apply]
    rw [this, h.col_zero i hi, f.map_zero]

end IsolatedEntry

/-! ### Helpers -/

private lemma sum_subtype_eq_of_zero_at_c
    {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*} [AddCommMonoid R]
    (f : ι → R) (c : ι) (hf : f c = 0) :
    (∑ k : DeletedIndex ι c, f k.1) = ∑ k : ι, f k := by
  have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := c)
  rw [hf, zero_add] at h
  exact h.symm

private lemma one_submatrix_left
    {ι : Type*} [DecidableEq ι] {R : Type*} [Semiring R]
    (c : ι) (i j : ι) (hi : i ≠ c) (hj : j ≠ c) :
    (1 : Matrix ι ι R) i j =
      (1 : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R)
        (⟨i, hi⟩ : DeletedIndex ι c) (⟨j, hj⟩ : DeletedIndex ι c) := by
  simp only [Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij]
  · have hij' : (⟨i, hi⟩ : DeletedIndex ι c) ≠ (⟨j, hj⟩ : DeletedIndex ι c) := by
      intro h
      apply hij
      exact congrArg Subtype.val h
    simp [hij, hij']

/-! ### Pivot unit -/

section PivotUnit

variable {e : GeneralLinearEquiv m n R} {r : m} {c : n}

private lemma iso_sum_val_inv_row_aux (h : IsolatedEntry e r c) (k : m) :
    e.val r c * e.inv c k = (1 : Matrix m m R) r k := by
  classical
  have hmul : (e.val * e.inv) r k = (1 : Matrix m m R) r k := by rw [e.val_inv]
  simp only [Matrix.mul_apply] at hmul
  have hz : ∀ j : n, j ≠ c → e.val r j * e.inv j k = 0 := by
    intro j hj
    rw [h.row_zero j hj, zero_mul]
  have hsum : ∑ j : n, e.val r j * e.inv j k = e.val r c * e.inv c k :=
    Fintype.sum_eq_single c (fun b hb => hz b hb)
  rw [hsum] at hmul
  exact hmul

private lemma iso_sum_inv_val_col_aux (h : IsolatedEntry e r c) (k : n) :
    e.inv k r * e.val r c = (1 : Matrix n n R) k c := by
  classical
  have hmul : (e.inv * e.val) k c = (1 : Matrix n n R) k c := by rw [e.inv_val]
  simp only [Matrix.mul_apply] at hmul
  have hz : ∀ i : m, i ≠ r → e.inv k i * e.val i c = 0 := by
    intro i hi
    rw [h.col_zero i hi, mul_zero]
  have hsum : ∑ i : m, e.inv k i * e.val i c = e.inv k r * e.val r c :=
    Fintype.sum_eq_single r (fun b hb => hz b hb)
  rw [hsum] at hmul
  exact hmul

def isolatedPivotUnit (h : IsolatedEntry e r c) : Rˣ where
  val := e.val r c
  inv := e.inv c r
  val_inv := by
    have h1 := iso_sum_val_inv_row_aux h (k := r)
    rw [Matrix.one_apply, ite_eq_left rfl] at h1
    exact h1
  inv_val := by
    have h1 := iso_sum_inv_val_col_aux h (k := c)
    rw [Matrix.one_apply, ite_eq_left rfl] at h1
    exact h1

@[simp]
theorem coe_isolatedPivotUnit (h : IsolatedEntry e r c) :
    (isolatedPivotUnit h : R) = e.val r c := rfl

theorem coe_inv_isolatedPivotUnit (h : IsolatedEntry e r c) :
    ((isolatedPivotUnit h)⁻¹ : Rˣ).val = e.inv c r := rfl

theorem isolatedPivotUnit_val_inv (h : IsolatedEntry e r c) :
    e.val r c * e.inv c r = 1 :=
  (isolatedPivotUnit h).val_inv

theorem isolatedPivotUnit_inv_val (h : IsolatedEntry e r c) :
    e.inv c r * e.val r c = 1 :=
  (isolatedPivotUnit h).inv_val

theorem inv_row_zero_of_ne (h : IsolatedEntry e r c) {i : m} (hi : i ≠ r) :
    e.inv c i = 0 := by
  have h1 : e.val r c * e.inv c i = 0 := by
    have := iso_sum_val_inv_row_aux h (k := i)
    rw [Matrix.one_apply, ite_eq_right (Ne.symm hi)] at this
    exact this
  have hunit : (isolatedPivotUnit h).inv * (e.val r c * e.inv c i) = e.inv c i := by
    calc (isolatedPivotUnit h).inv * (e.val r c * e.inv c i)
        = ((isolatedPivotUnit h).inv * e.val r c) * e.inv c i := by rw [mul_assoc]
      _ = ((isolatedPivotUnit h).inv * (isolatedPivotUnit h).val) * e.inv c i := by rfl
      _ = 1 * e.inv c i := by rw [(isolatedPivotUnit h).inv_val]
      _ = e.inv c i := by rw [one_mul]
  rw [h1, mul_zero] at hunit
  exact hunit.symm

theorem inv_col_zero_of_ne (h : IsolatedEntry e r c) {j : n} (hj : j ≠ c) :
    e.inv j r = 0 := by
  have h1 : e.inv j r * e.val r c = 0 := by
    have := iso_sum_inv_val_col_aux h (k := j)
    rw [Matrix.one_apply, ite_eq_right hj] at this
    exact this
  have hunit : (e.inv j r * e.val r c) * (isolatedPivotUnit h).inv = e.inv j r := by
    calc (e.inv j r * e.val r c) * (isolatedPivotUnit h).inv
        = e.inv j r * (e.val r c * (isolatedPivotUnit h).inv) := by rw [mul_assoc]
      _ = e.inv j r * ((isolatedPivotUnit h).val * (isolatedPivotUnit h).inv) := by rfl
      _ = e.inv j r * 1 := by rw [(isolatedPivotUnit h).val_inv]
      _ = e.inv j r := by rw [mul_one]
  rw [h1, zero_mul] at hunit
  exact hunit.symm

theorem isIsolated_symm (h : IsolatedEntry e r c) : IsolatedEntry e.symm c r where
  row_zero j hj := by
    simp only [val_symm]
    exact inv_row_zero_of_ne h hj
  col_zero i hi := by
    simp only [val_symm]
    exact inv_col_zero_of_ne h hi

end PivotUnit

theorem IsolatedEntry.symm {e : GeneralLinearEquiv m n R} {r : m} {c : n}
    (h : IsolatedEntry e r c) : IsolatedEntry e.symm c r :=
  isIsolated_symm h

/-! ### Reindexing -/

section Reindexing

variable {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']
variable {e : GeneralLinearEquiv m n R} {r : m} {c : n}

theorem IsolatedEntry.reindex (em : m' ≃ m) (en : n' ≃ n)
    (h : IsolatedEntry e r c) :
    IsolatedEntry (e.reindex em en) (em.symm r) (en.symm c) where
  row_zero j hj := by
    simp only [val_reindex, Matrix.submatrix_apply, Equiv.apply_symm_apply]
    have hj' : en j ≠ c := by
      intro heq
      apply hj
      calc j = en.symm (en j) := by simp
        _ = en.symm c := by rw [heq]
    exact h.row_zero (en j) hj'
  col_zero i hi := by
    simp only [val_reindex, Matrix.submatrix_apply, Equiv.apply_symm_apply]
    have hi' : em i ≠ r := by
      intro heq
      apply hi
      calc i = em.symm (em i) := by simp
        _ = em.symm r := by rw [heq]
    exact h.col_zero (em i) hi'

theorem IsolatedEntry.reindex_of_eq {r' : m'} {c' : n'} {em : m' ≃ m} {en : n' ≃ n}
    (hr : em r' = r) (hc : en c' = c) (h : IsolatedEntry e r c) :
    IsolatedEntry (e.reindex em en) r' c' where
  row_zero j hj := by
    simp only [val_reindex, Matrix.submatrix_apply, hr]
    have hj' : en j ≠ c := by
      intro heq
      apply hj
      have : en j = en c' := by rw [heq, hc]
      exact en.injective this
    exact h.row_zero (en j) hj'
  col_zero i hi := by
    simp only [val_reindex, Matrix.submatrix_apply, hc]
    have hi' : em i ≠ r := by
      intro heq
      apply hi
      have : em i = em r' := by rw [heq, hr]
      exact em.injective this
    exact h.col_zero (em i) hi'

end Reindexing

/-! ### Block insertion -/

section Insertion

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {R : Type*} [Semiring R]

def insertEntryVal (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    Matrix m n R :=
  fun i j =>
    if hi : i = r then
      if j = c then (a : R) else 0
    else
      if hj : j = c then 0
      else D.val (⟨i, hi⟩ : DeletedIndex m r) (⟨j, hj⟩ : DeletedIndex n c)

def insertEntryInvVal (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    Matrix n m R :=
  fun j i =>
    if hj : j = c then
      if i = r then ((a⁻¹ : Rˣ) : R) else 0
    else
      if hi : i = r then 0
      else D.inv (⟨j, hj⟩ : DeletedIndex n c) (⟨i, hi⟩ : DeletedIndex m r)

@[simp]
theorem insertEntryVal_self (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    insertEntryVal r c a D r c = (a : R) := by simp [insertEntryVal]

@[simp]
theorem insertEntryVal_row_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {j : n} (hj : j ≠ c) :
    insertEntryVal r c a D r j = 0 := by simp [insertEntryVal, hj]

@[simp]
theorem insertEntryVal_col_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {i : m} (hi : i ≠ r) :
    insertEntryVal r c a D i c = 0 := by simp [insertEntryVal, hi]

theorem insertEntryVal_ne_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {i : m} {j : n} (hi : i ≠ r) (hj : j ≠ c) :
    insertEntryVal r c a D i j =
      D.val (⟨i, hi⟩ : DeletedIndex m r) (⟨j, hj⟩ : DeletedIndex n c) := by
  simp [insertEntryVal, hi, hj]

@[simp]
theorem insertEntryInvVal_self (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    insertEntryInvVal r c a D c r = ((a⁻¹ : Rˣ) : R) := by simp [insertEntryInvVal]

@[simp]
theorem insertEntryInvVal_row_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {i : m} (hi : i ≠ r) :
    insertEntryInvVal r c a D c i = 0 := by simp [insertEntryInvVal, hi]

@[simp]
theorem insertEntryInvVal_col_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {j : n} (hj : j ≠ c) :
    insertEntryInvVal r c a D j r = 0 := by simp [insertEntryInvVal, hj]

theorem insertEntryInvVal_ne_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {j : n} {i : m} (hj : j ≠ c) (hi : i ≠ r) :
    insertEntryInvVal r c a D j i =
      D.inv (⟨j, hj⟩ : DeletedIndex n c) (⟨i, hi⟩ : DeletedIndex m r) := by
  simp [insertEntryInvVal, hj, hi]

lemma insertEntryVal_mul_insertEntryInvVal (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    insertEntryVal r c a D * insertEntryInvVal r c a D = 1 := by
  classical
  ext i k
  simp only [Matrix.mul_apply]
  by_cases hi : i = r
  · rw [hi]
    have hz : ∀ j : n, j ≠ c → insertEntryVal r c a D r j * insertEntryInvVal r c a D j k = 0 := by
      intro j hj
      rw [insertEntryVal_row_ne r c a D hj, zero_mul]
    have hsum : ∑ j : n, insertEntryVal r c a D r j * insertEntryInvVal r c a D j k =
        insertEntryVal r c a D r c * insertEntryInvVal r c a D c k :=
      Fintype.sum_eq_single c (fun b hb => hz b hb)
    rw [hsum, insertEntryVal_self]
    by_cases hk : k = r
    · rw [hk, insertEntryInvVal_self]
      have : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := by
        calc (a : R) * ((a⁻¹ : Rˣ) : R) = ((a * a⁻¹ : Rˣ) : R) := rfl
          _ = ((1 : Rˣ) : R) := by rw [mul_inv_cancel]
          _ = 1 := rfl
      rw [this, Matrix.one_apply, ite_eq_left rfl]
    · have hk' : k ≠ r := hk
      rw [insertEntryInvVal_row_ne r c a D hk', mul_zero]
      rw [Matrix.one_apply, ite_eq_right (Ne.symm hk')]
  · have hi' : i ≠ r := hi
    by_cases hk : k = r
    · rw [hk]
      have hz : ∀ j : n, insertEntryVal r c a D i j * insertEntryInvVal r c a D j r = 0 := by
        intro j
        by_cases hj : j = c
        · rw [hj, insertEntryVal_col_ne r c a D hi', zero_mul]
        · have hj' : j ≠ c := hj
          rw [insertEntryVal_ne_ne r c a D hi' hj', insertEntryInvVal_col_ne r c a D hj', mul_zero]
      have hsum : ∑ j : n, insertEntryVal r c a D i j * insertEntryInvVal r c a D j r = 0 :=
        Fintype.sum_eq_zero _ (fun j => hz j)
      rw [hsum, Matrix.one_apply, ite_eq_right hi']
    · have hk' : k ≠ r := hk
      let f : n → R := fun j => insertEntryVal r c a D i j * insertEntryInvVal r c a D j k
      have hf_c : f c = 0 := by dsimp [f]; rw [insertEntryVal_col_ne r c a D hi', zero_mul]
      have hsum_eq : (∑ j : n, f j) = ∑ d : DeletedIndex n c, f d.1 := by
        have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := c)
        rw [hf_c, zero_add] at h
        exact h
      have hf_eq : ∀ d : DeletedIndex n c,
          f d.1 = D.val (⟨i, hi'⟩ : DeletedIndex m r) d *
            D.inv d (⟨k, hk'⟩ : DeletedIndex m r) := by
        intro d
        dsimp [f]
        have hd : d.1 ≠ c := d.property
        rw [insertEntryVal_ne_ne r c a D hi' hd, insertEntryInvVal_ne_ne r c a D hd hk']
      have hsum_sub : (∑ d : DeletedIndex n c, f d.1) =
          (D.val * D.inv) (⟨i, hi'⟩ : DeletedIndex m r) (⟨k, hk'⟩ : DeletedIndex m r) := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro d _
        rw [hf_eq d]
      calc (∑ j : n, f j) = ∑ d : DeletedIndex n c, f d.1 := hsum_eq
        _ = (D.val * D.inv) (⟨i, hi'⟩ : DeletedIndex m r) (⟨k, hk'⟩ : DeletedIndex m r) := hsum_sub
        _ = (1 : Matrix (DeletedIndex m r) (DeletedIndex m r) R)
            (⟨i, hi'⟩ : DeletedIndex m r) (⟨k, hk'⟩ : DeletedIndex m r) := by rw [D.val_inv]
        _ = (1 : Matrix m m R) i k := (one_submatrix_left (R := R) r i k hi' hk').symm

lemma insertEntryInvVal_mul_insertEntryVal (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    insertEntryInvVal r c a D * insertEntryVal r c a D = 1 := by
  classical
  ext j l
  simp only [Matrix.mul_apply]
  by_cases hj : j = c
  · rw [hj]
    have hz : ∀ i : m, i ≠ r → insertEntryInvVal r c a D c i * insertEntryVal r c a D i l = 0 := by
      intro i hi
      rw [insertEntryInvVal_row_ne r c a D hi, zero_mul]
    have hsum : ∑ i : m, insertEntryInvVal r c a D c i * insertEntryVal r c a D i l =
        insertEntryInvVal r c a D c r * insertEntryVal r c a D r l :=
      Fintype.sum_eq_single r (fun b hb => hz b hb)
    rw [hsum, insertEntryInvVal_self]
    by_cases hl : l = c
    · rw [hl, insertEntryVal_self]
      have : ((a⁻¹ : Rˣ) : R) * (a : R) = 1 := by
        calc ((a⁻¹ : Rˣ) : R) * (a : R) = ((a⁻¹ * a : Rˣ) : R) := rfl
          _ = ((1 : Rˣ) : R) := by rw [inv_mul_cancel]
          _ = 1 := rfl
      rw [this, Matrix.one_apply, ite_eq_left rfl]
    · have hl' : l ≠ c := hl
      rw [insertEntryVal_row_ne r c a D hl', mul_zero, Matrix.one_apply, ite_eq_right (Ne.symm hl')]
  · have hj' : j ≠ c := hj
    by_cases hl : l = c
    · rw [hl]
      have hz : ∀ i : m, insertEntryInvVal r c a D j i * insertEntryVal r c a D i c = 0 := by
        intro i
        by_cases hi : i = r
        · rw [hi, insertEntryInvVal_col_ne r c a D hj', zero_mul]
        · have hi' : i ≠ r := hi
          rw [insertEntryVal_col_ne r c a D hi', mul_zero]
      have hsum : ∑ i : m, insertEntryInvVal r c a D j i * insertEntryVal r c a D i c = 0 :=
        Fintype.sum_eq_zero _ (fun i => hz i)
      rw [hsum, Matrix.one_apply, ite_eq_right hj']
    · have hl' : l ≠ c := hl
      let f : m → R := fun i => insertEntryInvVal r c a D j i * insertEntryVal r c a D i l
      have hf_r : f r = 0 := by dsimp [f]; rw [insertEntryInvVal_col_ne r c a D hj', zero_mul]
      have hsum_eq : (∑ i : m, f i) = ∑ d : DeletedIndex m r, f d.1 := by
        have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := r)
        rw [hf_r, zero_add] at h
        exact h
      have hf_eq : ∀ d : DeletedIndex m r,
          f d.1 = D.inv (⟨j, hj'⟩ : DeletedIndex n c) d *
            D.val d (⟨l, hl'⟩ : DeletedIndex n c) := by
        intro d
        dsimp [f]
        have hd : d.1 ≠ r := d.property
        rw [insertEntryInvVal_ne_ne r c a D hj' hd, insertEntryVal_ne_ne r c a D hd hl']
      have hsum_sub : (∑ d : DeletedIndex m r, f d.1) =
          (D.inv * D.val) (⟨j, hj'⟩ : DeletedIndex n c) (⟨l, hl'⟩ : DeletedIndex n c) := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro d _
        rw [hf_eq d]
      calc (∑ i : m, f i) = ∑ d : DeletedIndex m r, f d.1 := hsum_eq
        _ = (D.inv * D.val) (⟨j, hj'⟩ : DeletedIndex n c) (⟨l, hl'⟩ : DeletedIndex n c) := hsum_sub
        _ = (1 : Matrix (DeletedIndex n c) (DeletedIndex n c) R)
            (⟨j, hj'⟩ : DeletedIndex n c) (⟨l, hl'⟩ : DeletedIndex n c) := by rw [D.inv_val]
        _ = (1 : Matrix n n R) j l := (one_submatrix_left (R := R) c j l hj' hl').symm

def insertEntryEquiv (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    GeneralLinearEquiv m n R where
  val := insertEntryVal r c a D
  inv := insertEntryInvVal r c a D
  val_inv := insertEntryVal_mul_insertEntryInvVal r c a D
  inv_val := insertEntryInvVal_mul_insertEntryVal r c a D

@[simp]
theorem val_insertEntryEquiv (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    (insertEntryEquiv r c a D).val = insertEntryVal r c a D := rfl

@[simp]
theorem inv_insertEntryEquiv (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    (insertEntryEquiv r c a D).inv = insertEntryInvVal r c a D := rfl

@[simp]
theorem insertEntryEquiv_val_self (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    (insertEntryEquiv r c a D).val r c = (a : R) := by
  simp [val_insertEntryEquiv, insertEntryVal]

@[simp]
theorem insertEntryEquiv_val_row_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {j : n} (hj : j ≠ c) :
    (insertEntryEquiv r c a D).val r j = 0 :=
  insertEntryVal_row_ne r c a D hj

@[simp]
theorem insertEntryEquiv_val_col_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {i : m} (hi : i ≠ r) :
    (insertEntryEquiv r c a D).val i c = 0 :=
  insertEntryVal_col_ne r c a D hi

theorem insertEntryEquiv_val_ne_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {i : m} {j : n} (hi : i ≠ r) (hj : j ≠ c) :
    (insertEntryEquiv r c a D).val i j =
      D.val (⟨i, hi⟩ : DeletedIndex m r) (⟨j, hj⟩ : DeletedIndex n c) :=
  insertEntryVal_ne_ne r c a D hi hj

@[simp]
theorem insertEntryEquiv_inv_self (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    (insertEntryEquiv r c a D).inv c r = ((a⁻¹ : Rˣ) : R) := by
  simp [inv_insertEntryEquiv, insertEntryInvVal]

@[simp]
theorem insertEntryEquiv_inv_row_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {i : m} (hi : i ≠ r) :
    (insertEntryEquiv r c a D).inv c i = 0 :=
  insertEntryInvVal_row_ne r c a D hi

@[simp]
theorem insertEntryEquiv_inv_col_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {j : n} (hj : j ≠ c) :
    (insertEntryEquiv r c a D).inv j r = 0 :=
  insertEntryInvVal_col_ne r c a D hj

theorem insertEntryEquiv_inv_ne_ne (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    {j : n} {i : m} (hj : j ≠ c) (hi : i ≠ r) :
    (insertEntryEquiv r c a D).inv j i =
      D.inv (⟨j, hj⟩ : DeletedIndex n c) (⟨i, hi⟩ : DeletedIndex m r) :=
  insertEntryInvVal_ne_ne r c a D hj hi

theorem isIsolated_insertEntryEquiv (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    IsolatedEntry (insertEntryEquiv r c a D) r c where
  row_zero _ hj := insertEntryEquiv_val_row_ne r c a D hj
  col_zero _ hi := insertEntryEquiv_val_col_ne r c a D hi

theorem symm_insertEntryEquiv (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    (insertEntryEquiv r c a D).symm = insertEntryEquiv c r a⁻¹ D.symm := by
  apply ext
  ext j i
  by_cases hj : j = c
  · by_cases hi : i = r
    · subst hj; subst hi
      simp
    · subst hj
      simp [hi]
  · by_cases hi : i = r
    · subst hi
      simp [hj]
    · simp only [val_symm, inv_insertEntryEquiv, val_insertEntryEquiv,
        insertEntryVal, insertEntryInvVal, hj, hi]

theorem map_insertEntryEquiv (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R)
    (f : R →+* S) :
    (insertEntryEquiv r c a D).map f =
      insertEntryEquiv r c (Units.map f a) (D.map f) := by
  apply ext
  ext i j
  simp only [val_map, Matrix.map_apply, val_insertEntryEquiv, insertEntryVal]
  by_cases hi : i = r
  · by_cases hj : j = c
    · simp [hi, hj]
    · simp [hi, hj]
  · by_cases hj : j = c
    · simp [hi, hj]
    · simp [hi, hj]

end Insertion

/-! ### Deletion -/

section Deletion

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {R : Type*} [Semiring R]
variable {e : GeneralLinearEquiv m n R} {r : m} {c : n}

def deleteEntryVal (_h : IsolatedEntry e r c) :
    Matrix (DeletedIndex m r) (DeletedIndex n c) R :=
  e.val.submatrix Subtype.val Subtype.val

def deleteEntryInvVal (_h : IsolatedEntry e r c) :
    Matrix (DeletedIndex n c) (DeletedIndex m r) R :=
  e.inv.submatrix Subtype.val Subtype.val

theorem deleteEntryVal_apply (_h : IsolatedEntry e r c)
    (i : DeletedIndex m r) (j : DeletedIndex n c) :
    deleteEntryVal _h i j = e.val i.1 j.1 := rfl

theorem deleteEntryInvVal_apply (_h : IsolatedEntry e r c)
    (i : DeletedIndex n c) (j : DeletedIndex m r) :
    deleteEntryInvVal _h i j = e.inv i.1 j.1 := rfl

lemma deleteEntryVal_mul_deleteEntryInvVal (h : IsolatedEntry e r c) :
    deleteEntryVal h * deleteEntryInvVal h = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, deleteEntryVal_apply, deleteEntryInvVal_apply]
  set f : n → R := fun k => e.val i.1 k * e.inv k j.1
  have hf : f c = 0 := by dsimp [f]; rw [h.col_zero i.1 i.2, zero_mul]
  have hsum_full : (e.val * e.inv) i.1 j.1 = ∑ k : n, f k := by simp [f, Matrix.mul_apply]
  have hsum_del : (∑ k : DeletedIndex n c, f k.1) = ∑ k : n, f k :=
    sum_subtype_eq_of_zero_at_c f c hf
  calc (∑ k : DeletedIndex n c, e.val i.1 k.1 * e.inv k.1 j.1)
      = ∑ k : DeletedIndex n c, f k.1 := rfl
    _ = ∑ k : n, f k := hsum_del
    _ = (e.val * e.inv) i.1 j.1 := hsum_full.symm
    _ = (1 : Matrix m m R) i.1 j.1 := by rw [e.val_inv]
    _ = (1 : Matrix (DeletedIndex m r) (DeletedIndex m r) R) i j := by
        simp only [Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · have hij_val : i.1 ≠ j.1 := by
            intro heq
            apply hij
            exact Subtype.ext heq
          simp [hij, hij_val]

lemma deleteEntryInvVal_mul_deleteEntryVal (h : IsolatedEntry e r c) :
    deleteEntryInvVal h * deleteEntryVal h = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, deleteEntryVal_apply, deleteEntryInvVal_apply]
  set f : m → R := fun k => e.inv i.1 k * e.val k j.1
  have hf : f r = 0 := by dsimp [f]; rw [h.row_zero j.1 j.2, mul_zero]
  have hsum_full : (e.inv * e.val) i.1 j.1 = ∑ k : m, f k := by simp [f, Matrix.mul_apply]
  have hsum_del : (∑ k : DeletedIndex m r, f k.1) = ∑ k : m, f k :=
    sum_subtype_eq_of_zero_at_c f r hf
  calc (∑ k : DeletedIndex m r, e.inv i.1 k.1 * e.val k.1 j.1)
      = ∑ k : DeletedIndex m r, f k.1 := rfl
    _ = ∑ k : m, f k := hsum_del
    _ = (e.inv * e.val) i.1 j.1 := hsum_full.symm
    _ = (1 : Matrix n n R) i.1 j.1 := by rw [e.inv_val]
    _ = (1 : Matrix (DeletedIndex n c) (DeletedIndex n c) R) i j := by
        simp only [Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · have hij_val : i.1 ≠ j.1 := by
            intro heq
            apply hij
            exact Subtype.ext heq
          simp [hij, hij_val]

def deleteEntryEquiv (h : IsolatedEntry e r c) :
    GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R where
  val := deleteEntryVal h
  inv := deleteEntryInvVal h
  val_inv := deleteEntryVal_mul_deleteEntryInvVal h
  inv_val := deleteEntryInvVal_mul_deleteEntryVal h

@[simp]
theorem val_deleteEntryEquiv (_h : IsolatedEntry e r c) :
    (deleteEntryEquiv _h).val = deleteEntryVal _h := rfl

@[simp]
theorem inv_deleteEntryEquiv (_h : IsolatedEntry e r c) :
    (deleteEntryEquiv _h).inv = deleteEntryInvVal _h := rfl

theorem val_deleteEntryEquiv_apply (_h : IsolatedEntry e r c)
    (i : DeletedIndex m r) (j : DeletedIndex n c) :
    (deleteEntryEquiv _h).val i j = e.val i.1 j.1 := rfl

theorem inv_deleteEntryEquiv_apply (_h : IsolatedEntry e r c)
    (i : DeletedIndex n c) (j : DeletedIndex m r) :
    (deleteEntryEquiv _h).inv i j = e.inv i.1 j.1 := rfl

theorem delete_after_insert (r : m) (c : n) (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex m r) (DeletedIndex n c) R) :
    deleteEntryEquiv (isIsolated_insertEntryEquiv r c a D) = D := by
  apply ext
  ext i j
  have hi : i.val ≠ r := i.property
  have hj : j.val ≠ c := j.property
  simp only [val_deleteEntryEquiv, deleteEntryVal, val_insertEntryEquiv]
  calc insertEntryVal r c a D i.val j.val
      = D.val ⟨i.val, hi⟩ ⟨j.val, hj⟩ := insertEntryVal_ne_ne r c a D hi hj
    _ = D.val i j := by
        have hi_eq : (⟨i.val, hi⟩ : DeletedIndex m r) = i := Subtype.ext rfl
        have hj_eq : (⟨j.val, hj⟩ : DeletedIndex n c) = j := Subtype.ext rfl
        rw [hi_eq, hj_eq]

theorem insert_delete_reconstruction (h : IsolatedEntry e r c) :
    insertEntryEquiv r c (isolatedPivotUnit h) (deleteEntryEquiv h) = e := by
  apply ext
  ext i j
  by_cases hi : i = r
  · rw [hi]
    by_cases hj : j = c
    · rw [hj]
      simp only [val_insertEntryEquiv, insertEntryVal_self, coe_isolatedPivotUnit]
    · have hrj : e.val r j = 0 := h.row_zero j hj
      have hleft : (insertEntryEquiv r c (isolatedPivotUnit h) (deleteEntryEquiv h)).val r j = 0 :=
        insertEntryEquiv_val_row_ne r c _ _ hj
      rw [hleft, hrj]
  · have hi' : i ≠ r := hi
    by_cases hj : j = c
    · rw [hj]
      have hic : e.val i c = 0 := h.col_zero i hi'
      have hleft : (insertEntryEquiv r c (isolatedPivotUnit h) (deleteEntryEquiv h)).val i c = 0 :=
        insertEntryEquiv_val_col_ne r c _ _ hi'
      rw [hleft, hic]
    · have hj' : j ≠ c := hj
      calc (insertEntryEquiv r c (isolatedPivotUnit h) (deleteEntryEquiv h)).val i j
          = (deleteEntryEquiv h).val ⟨i, hi'⟩ ⟨j, hj'⟩ :=
            insertEntryEquiv_val_ne_ne r c _ _ hi' hj'
        _ = e.val i j := rfl

theorem eq_of_pivot_and_delete_eq {e₁ e₂ : GeneralLinearEquiv m n R}
    {r : m} {c : n} {h₁ : IsolatedEntry e₁ r c} {h₂ : IsolatedEntry e₂ r c}
    (hpivot : e₁.val r c = e₂.val r c)
    (hdel : deleteEntryEquiv h₁ = deleteEntryEquiv h₂) :
    e₁ = e₂ := by
  have h1 := insert_delete_reconstruction h₁
  have h2 := insert_delete_reconstruction h₂
  have hpivot_units : isolatedPivotUnit h₁ = isolatedPivotUnit h₂ := by
    apply Units.ext
    exact hpivot
  calc e₁ = insertEntryEquiv r c (isolatedPivotUnit h₁) (deleteEntryEquiv h₁) := h1.symm
    _ = insertEntryEquiv r c (isolatedPivotUnit h₂) (deleteEntryEquiv h₂) := by
        rw [hpivot_units, hdel]
    _ = e₂ := h2

theorem map_deleteEntryEquiv (h : IsolatedEntry e r c) (f : R →+* S) :
    (deleteEntryEquiv h).map f = deleteEntryEquiv (h.map f) := by
  apply ext
  ext i j
  simp [val_map, Matrix.map_apply, deleteEntryVal, Matrix.submatrix_apply]

end Deletion

/-! ### Square compatibility bridges -/

section SquareBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Semiring R]
variable (c : ι)

theorem toGL_insertEntryEquiv_val (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex ι c) (DeletedIndex ι c) R) (i j : ι) :
    insertEntryVal (m := ι) (n := ι) c c a D i j =
      insertVal (R := R) c a (toGL D) i j := by
  simp only [insertEntryVal, insertVal, val_toGL]

theorem toGL_insertEntryEquiv (a : Rˣ)
    (D : GeneralLinearEquiv (DeletedIndex ι c) (DeletedIndex ι c) R) :
    toGL (insertEntryEquiv (m := ι) (n := ι) c c a D) =
      insertCoordinateUnit c a (toGL D) := by
  apply Units.ext
  ext i j
  simp only [toGL, Units.val_mk, coe_insertCoordinateUnit]
  exact toGL_insertEntryEquiv_val c a D i j

theorem ofGL_insertCoordinateUnit (a : Rˣ) (x : GL (DeletedIndex ι c) R) :
    ofGL (insertCoordinateUnit c a x) =
      insertEntryEquiv (m := ι) (n := ι) c c a (ofGL x) := by
  apply ext
  ext i j
  simp only [val_insertEntryEquiv, insertEntryVal, coe_insertCoordinateUnit, insertVal,
    val_ofGL]

variable {R' : Type*} [Ring R']

theorem IsolatedCoordinate.toIsolatedEntry {g : GL ι R'} {c : ι}
    (h : IsolatedCoordinate g c) : IsolatedEntry (ofGL g) c c where
  row_zero j hj := by
    have : (↑g : Matrix ι ι R') c j = 0 := h.row_zero j hj
    simpa [ofGL] using this
  col_zero i hi := by
    have : (↑g : Matrix ι ι R') i c = 0 := h.col_zero i hi
    simpa [ofGL] using this

theorem IsolatedEntry.toIsolatedCoordinate {e : GeneralLinearEquiv ι ι R'} {c : ι}
    (h : IsolatedEntry e c c) : IsolatedCoordinate (toGL e) c where
  col_zero i hi := by
    have : e.val i c = 0 := h.col_zero i hi
    simpa [toGL] using this
  row_zero j hj := by
    have : e.val c j = 0 := h.row_zero j hj
    simpa [toGL] using this

theorem isolatedPivotUnit_toGL {e : GeneralLinearEquiv ι ι R'} {c : ι}
    (h : IsolatedEntry e c c) :
    isolatedPivotUnit h =
      Matrix.GeneralLinearGroup.isolatedPivotUnit c (toGL e) h.toIsolatedCoordinate := by
  apply Units.ext
  rfl

theorem delete_toGL {e : GeneralLinearEquiv ι ι R'} {c : ι}
    (h : IsolatedEntry e c c) :
    toGL (deleteEntryEquiv h) = deleteCoordinate (toGL e) c h.toIsolatedCoordinate := by
  apply Units.ext
  ext i j
  rfl

theorem ofGL_reconstruction {g : GL ι R'} {c : ι} (h : IsolatedCoordinate g c) :
    ofGL g = insertEntryEquiv (m := ι) (n := ι) c c
      (Matrix.GeneralLinearGroup.isolatedPivotUnit c g h) (ofGL (deleteCoordinate g c h)) := by
  calc ofGL g =
        ofGL (insertCoordinateUnit c
          (Matrix.GeneralLinearGroup.isolatedPivotUnit c g h) (deleteCoordinate g c h)) := by
        rw [insert_isolatedPivotUnit_deleteCoordinate]
    _ = insertEntryEquiv c c
          (Matrix.GeneralLinearGroup.isolatedPivotUnit c g h)
          (ofGL (deleteCoordinate g c h)) := by
        rw [ofGL_insertCoordinateUnit]

end SquareBridge

end GeneralLinearEquiv

end Matrix
