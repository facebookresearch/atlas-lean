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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementarySweep

/-!
# Rectangular formulas for upper elementary sweeps

Over a ring with a finite ordered active index set, row and column elementary
sweeps act on rectangular matrices with an arbitrary other index set. Entry
formulas express the changed rows and columns as finite sums and identify the
entries that remain fixed.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix Finset Function

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [Ring R]

section RowRectangular

variable {κ : Type*}

theorem rowSingle_mul_entry_rect (r : ι) (v : RowIdx ι r → Multiplicative R)
    (i : RowIdx ι r) (M : Matrix ι κ R) (p : ι) (q : κ) :
    (rowSingle r v i * M) p q =
      if p = i.val then (v i).toAdd * M r q else 0 := by
  unfold rowSingle
  by_cases hp : p = i.val
  · subst hp
    have h1 : (Matrix.single i.val r (v i).toAdd * M) i.val q =
        (v i).toAdd * M r q := by
      calc (Matrix.single i.val r (v i).toAdd * M) i.val q
          = ∑ x, (Matrix.single i.val r (v i).toAdd) i.val x * M x q := by
            rw [Matrix.mul_apply]
        _ = ∑ x, (if r = x then (v i).toAdd else 0) * M x q := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : r = x
            · simp [hx]
            · simp [hx]
        _ = (v i).toAdd * M r q := by
            rw [Finset.sum_eq_single r]
            · simp
            · intro b _ hb
              have : r ≠ b := fun h => hb h.symm
              simp [this]
            · simp
    simp [h1]
  · have h_zero : (Matrix.single i.val r (v i).toAdd * M) p q = 0 := by
      calc (Matrix.single i.val r (v i).toAdd * M) p q
          = ∑ x, (Matrix.single i.val r (v i).toAdd) p x * M x q := by
            rw [Matrix.mul_apply]
        _ = 0 := by
            apply Finset.sum_eq_zero
            intro x _
            have : Matrix.single i.val r (v i).toAdd p x = 0 := by
              have : ¬(i.val = p ∧ r = x) := by
                intro ⟨hp', _⟩
                exact hp hp'.symm
              rw [Matrix.single_apply]
              rw [ite_eq_right this]
            simp [this]
    simp [hp, h_zero]

theorem rowSum_mul_apply_finset_rect (r : ι) (v : RowIdx ι r → Multiplicative R)
    (s : Finset (RowIdx ι r)) (M : Matrix ι κ R) (i : ι) (j : κ) :
    ((∑ k ∈ s, rowSingle r v k) * M) i j =
      ∑ k ∈ s, (rowSingle r v k * M) i j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    calc ((∑ k ∈ insert a s, rowSingle r v k) * M) i j
        = ((rowSingle r v a + ∑ k ∈ s, rowSingle r v k) * M) i j := by
          rw [Finset.sum_insert ha]
      _ = (rowSingle r v a * M + (∑ k ∈ s, rowSingle r v k) * M) i j := by
          rw [Matrix.add_mul]
      _ = (rowSingle r v a * M) i j + ((∑ k ∈ s, rowSingle r v k) * M) i j := by
          rw [Matrix.add_apply]
      _ = (rowSingle r v a * M) i j + ∑ k ∈ s, (rowSingle r v k * M) i j := by
          rw [ih]
      _ = ∑ k ∈ insert a s, (rowSingle r v k * M) i j := by
          rw [Finset.sum_insert ha]

theorem rowSum_mul_entry_rect (r : ι) (v : RowIdx ι r → Multiplicative R)
    (s : Finset (RowIdx ι r)) (M : Matrix ι κ R) (i : ι) (j : κ) :
    ((∑ k ∈ s, rowSingle r v k) * M) i j =
      ∑ k ∈ s, if i = k.val then (v k).toAdd * M r j else 0 := by
  classical
  calc ((∑ k ∈ s, rowSingle r v k) * M) i j
      = ∑ k ∈ s, (rowSingle r v k * M) i j :=
        rowSum_mul_apply_finset_rect r v s M i j
    _ = ∑ k ∈ s, if i = k.val then (v k).toAdd * M r j else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        exact rowSingle_mul_entry_rect r v k M i j

theorem rowSum_mul_apply_rect (r : ι) (v : RowIdx ι r → Multiplicative R)
    (M : Matrix ι κ R) (i : ι) (j : κ) :
    (rowSum r v * M) i j =
      if h : i < r then (v ⟨i, h⟩).toAdd * M r j else 0 := by
  classical
  have h_general := rowSum_mul_entry_rect r v Finset.univ M i j
  unfold rowSum at h_general ⊢
  rw [h_general]
  by_cases hi : i < r
  · have h_eq : (∑ k : RowIdx ι r,
          if i = k.val then (v k).toAdd * M r j else 0) =
        (v ⟨i, hi⟩).toAdd * M r j := by
      have h_eq2 : ∀ (k : RowIdx ι r),
          (if i = k.val then (v k).toAdd * M r j else 0) =
            if k = ⟨i, hi⟩ then (v ⟨i, hi⟩).toAdd * M r j else 0 := by
        intro k
        by_cases hk : k = ⟨i, hi⟩
        · subst hk
          simp
        · have hval : ¬(i = k.val) := by
            intro heq
            apply hk
            exact Subtype.ext heq.symm
          simp [hval, hk]
      calc (∑ k : RowIdx ι r, if i = k.val then (v k).toAdd * M r j else 0)
          = ∑ k : RowIdx ι r,
              if k = ⟨i, hi⟩ then (v ⟨i, hi⟩).toAdd * M r j else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            exact h_eq2 k
        _ = (v ⟨i, hi⟩).toAdd * M r j := by
            rw [Finset.sum_eq_single (⟨i, hi⟩ : RowIdx ι r)]
            · simp
            · intro b _ hb
              simp [hb]
            · intro hb
              exact absurd (Finset.mem_univ _) hb
    rw [h_eq]
    simp [hi]
  · have h_all_zero : ∀ (k : RowIdx ι r),
        (if i = k.val then (v k).toAdd * M r j else 0) = 0 := by
      intro k
      have hval : ¬(i = k.val) := by
        intro heq
        have : i < r := heq ▸ k.prop
        exact hi this
      simp [hval]
    have : (∑ k : RowIdx ι r,
        if i = k.val then (v k).toAdd * M r j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact h_all_zero k
    rw [this]
    simp [hi]

theorem rowSweep_mul_apply_rect (r : ι) (v : RowIdx ι r → Multiplicative R)
    (M : Matrix ι κ R) (i : ι) (j : κ) :
    (((rowSweep r v : GL ι R) : Matrix ι ι R) * M) i j =
      if h : i < r then M i j + (v ⟨i, h⟩).toAdd * M r j else M i j := by
  classical
  have h_eq : (↑(rowSweep r v) : Matrix ι ι R) = 1 + rowSum r v :=
    coe_rowSweep r v
  calc (((rowSweep r v : GL ι R) : Matrix ι ι R) * M) i j
      = (((1 : Matrix ι ι R) + rowSum r v) * M) i j := by rw [h_eq]
    _ = (M + (rowSum r v * M)) i j := by rw [Matrix.add_mul, Matrix.one_mul]
    _ = M i j + (rowSum r v * M) i j := by rw [Matrix.add_apply]
    _ = if h : i < r then M i j + (v ⟨i, h⟩).toAdd * M r j else M i j := by
        rw [rowSum_mul_apply_rect]
        by_cases hi : i < r <;> simp [hi]

theorem rowSweep_mul_apply_same_row_rect (r : ι)
    (v : RowIdx ι r → Multiplicative R) (M : Matrix ι κ R) (j : κ) :
    (((rowSweep r v : GL ι R) : Matrix ι ι R) * M) r j = M r j := by
  have h := rowSweep_mul_apply_rect r v M r j
  have hr : ¬(r < r) := lt_irrefl r
  simp only [hr, dite_false] at h
  exact h

theorem rowSweep_mul_apply_of_not_lt_rect (r : ι)
    (v : RowIdx ι r → Multiplicative R) (M : Matrix ι κ R)
    (i : ι) (j : κ) (h : ¬(i < r)) :
    (((rowSweep r v : GL ι R) : Matrix ι ι R) * M) i j = M i j := by
  have h_eq := rowSweep_mul_apply_rect r v M i j
  simp only [h, dite_false] at h_eq
  exact h_eq

end RowRectangular

section ColRectangular

variable {κ : Type*}

theorem colSingle_mul_entry_rect (c : ι) (v : ColIdx ι c → Multiplicative R)
    (j : ColIdx ι c) (M : Matrix κ ι R) (p : κ) (q : ι) :
    (M * colSingle c v j) p q =
      if q = j.val then M p c * (v j).toAdd else 0 := by
  unfold colSingle
  by_cases hq : q = j.val
  · subst hq
    have h1 : (M * Matrix.single c j.val (v j).toAdd) p j.val =
        M p c * (v j).toAdd := by
      calc (M * Matrix.single c j.val (v j).toAdd) p j.val
          = ∑ x, M p x * (Matrix.single c j.val (v j).toAdd) x j.val := by
            rw [Matrix.mul_apply]
        _ = ∑ x, M p x * (if c = x then (v j).toAdd else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : c = x
            · simp [hx]
            · simp [hx]
        _ = M p c * (v j).toAdd := by
            rw [Finset.sum_eq_single c]
            · simp
            · intro b _ hb
              have : c ≠ b := fun h => hb h.symm
              simp [this]
            · simp
    simp [h1]
  · have h_zero : (M * Matrix.single c j.val (v j).toAdd) p q = 0 := by
      calc (M * Matrix.single c j.val (v j).toAdd) p q
          = ∑ x, M p x * (Matrix.single c j.val (v j).toAdd) x q := by
            rw [Matrix.mul_apply]
        _ = 0 := by
            apply Finset.sum_eq_zero
            intro x _
            have : Matrix.single c j.val (v j).toAdd x q = 0 := by
              have : ¬(c = x ∧ j.val = q) := by
                intro ⟨_, hq_eq⟩
                exact hq hq_eq.symm
              rw [Matrix.single_apply]
              rw [ite_eq_right this]
            simp [this]
    simp [hq, h_zero]

theorem colSum_mul_aux_finset_rect (c : ι) (v : ColIdx ι c → Multiplicative R)
    (s : Finset (ColIdx ι c)) (M : Matrix κ ι R) (i : κ) (j : ι) :
    (M * (∑ k ∈ s, colSingle c v k)) i j =
      ∑ k ∈ s, (M * colSingle c v k) i j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    calc (M * (∑ k ∈ insert a s, colSingle c v k)) i j
        = (M * (colSingle c v a + ∑ k ∈ s, colSingle c v k)) i j := by
          rw [Finset.sum_insert ha]
      _ = (M * colSingle c v a + M * (∑ k ∈ s, colSingle c v k)) i j := by
          rw [Matrix.mul_add]
      _ = (M * colSingle c v a) i j + (M * (∑ k ∈ s, colSingle c v k)) i j := by
          rw [Matrix.add_apply]
      _ = (M * colSingle c v a) i j + ∑ k ∈ s, (M * colSingle c v k) i j := by
          rw [ih]
      _ = ∑ k ∈ insert a s, (M * colSingle c v k) i j := by
          rw [Finset.sum_insert ha]

theorem colSum_mul_entry_rect (c : ι) (v : ColIdx ι c → Multiplicative R)
    (s : Finset (ColIdx ι c)) (M : Matrix κ ι R) (i : κ) (j : ι) :
    (M * (∑ k ∈ s, colSingle c v k)) i j =
      ∑ k ∈ s, if j = k.val then M i c * (v k).toAdd else 0 := by
  classical
  calc (M * (∑ k ∈ s, colSingle c v k)) i j
      = ∑ k ∈ s, (M * colSingle c v k) i j :=
        colSum_mul_aux_finset_rect c v s M i j
    _ = ∑ k ∈ s, if j = k.val then M i c * (v k).toAdd else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        exact colSingle_mul_entry_rect c v k M i j

theorem colSum_mul_apply_rect (c : ι) (v : ColIdx ι c → Multiplicative R)
    (M : Matrix κ ι R) (i : κ) (j : ι) :
    (M * colSum c v) i j =
      if h : c < j then M i c * (v ⟨j, h⟩).toAdd else 0 := by
  classical
  have h_general := colSum_mul_entry_rect c v Finset.univ M i j
  unfold colSum at h_general ⊢
  rw [h_general]
  by_cases hj : c < j
  · have h_eq : (∑ k : ColIdx ι c,
          if j = k.val then M i c * (v k).toAdd else 0) =
        M i c * (v ⟨j, hj⟩).toAdd := by
      have h_eq2 : ∀ (k : ColIdx ι c),
          (if j = k.val then M i c * (v k).toAdd else 0) =
            if k = ⟨j, hj⟩ then M i c * (v ⟨j, hj⟩).toAdd else 0 := by
        intro k
        by_cases hk : k = ⟨j, hj⟩
        · subst hk
          simp
        · have hval : ¬(j = k.val) := by
            intro heq
            apply hk
            exact Subtype.ext heq.symm
          simp [hval, hk]
      calc (∑ k : ColIdx ι c, if j = k.val then M i c * (v k).toAdd else 0)
          = ∑ k : ColIdx ι c,
              if k = ⟨j, hj⟩ then M i c * (v ⟨j, hj⟩).toAdd else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            exact h_eq2 k
        _ = M i c * (v ⟨j, hj⟩).toAdd := by
            rw [Finset.sum_eq_single (⟨j, hj⟩ : ColIdx ι c)]
            · simp
            · intro b _ hb
              simp [hb]
            · intro hb
              exact absurd (Finset.mem_univ _) hb
    rw [h_eq]
    simp [hj]
  · have h_all_zero : ∀ (k : ColIdx ι c),
        (if j = k.val then M i c * (v k).toAdd else 0) = 0 := by
      intro k
      have hval : ¬(j = k.val) := by
        intro heq
        have : c < j := heq ▸ k.prop
        exact hj this
      simp [hval]
    have : (∑ k : ColIdx ι c,
        if j = k.val then M i c * (v k).toAdd else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact h_all_zero k
    rw [this]
    simp [hj]

theorem columnSweep_mul_apply_rect (c : ι) (v : ColIdx ι c → Multiplicative R)
    (M : Matrix κ ι R) (i : κ) (j : ι) :
    (M * ((columnSweep c v : GL ι R) : Matrix ι ι R)) i j =
      if h : c < j then M i j + M i c * (v ⟨j, h⟩).toAdd else M i j := by
  classical
  have h_eq : (↑(columnSweep c v) : Matrix ι ι R) = 1 + colSum c v :=
    coe_columnSweep c v
  calc (M * ((columnSweep c v : GL ι R) : Matrix ι ι R)) i j
      = (M * ((1 : Matrix ι ι R) + colSum c v)) i j := by rw [h_eq]
    _ = (M + M * colSum c v) i j := by rw [Matrix.mul_add, Matrix.mul_one]
    _ = M i j + (M * colSum c v) i j := by rw [Matrix.add_apply]
    _ = if h : c < j then M i j + M i c * (v ⟨j, h⟩).toAdd else M i j := by
        rw [colSum_mul_apply_rect]
        by_cases hj : c < j <;> simp [hj]

theorem columnSweep_mul_apply_same_col_rect (c : ι)
    (v : ColIdx ι c → Multiplicative R) (M : Matrix κ ι R) (i : κ) :
    (M * ((columnSweep c v : GL ι R) : Matrix ι ι R)) i c = M i c := by
  have h := columnSweep_mul_apply_rect c v M i c
  have hc : ¬(c < c) := lt_irrefl c
  simp only [hc, dite_false] at h
  exact h

theorem columnSweep_mul_apply_of_not_gt_rect (c : ι)
    (v : ColIdx ι c → Multiplicative R) (M : Matrix κ ι R)
    (i : κ) (j : ι) (h : ¬(c < j)) :
    (M * ((columnSweep c v : GL ι R) : Matrix ι ι R)) i j = M i j := by
  have h_eq := columnSweep_mul_apply_rect c v M i j
  simp only [h, dite_false] at h_eq
  exact h_eq

end ColRectangular

end Matrix.GeneralLinearGroup
