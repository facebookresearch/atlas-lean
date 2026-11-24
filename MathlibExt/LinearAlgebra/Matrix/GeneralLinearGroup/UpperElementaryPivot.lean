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
# Pivot clearing via division for upper-elementary sweeps

Specialization of the ring-generic `rowSweep` / `columnSweep` API to
explicit inverse-pivot coefficients. This is the first layer allowed to
assume division.

For `[DivisionRing K]` and `M : Matrix ι ι K`, `r c : ι`, `hp : M r c ≠ 0`,

* `rowClearCoeffs` uses coefficient `-(M i c) * (M r c)⁻¹` so that left row
  addition `row_i ← row_i + coeff * row_r` clears the `c`-column above `r`.
* `columnClearCoeffs` uses `-(M r c)⁻¹ * M r j` so right column addition
  `col_j ← col_j + col_c * coeff` clears the `r`-row to the right of `c`.

Assumptions are kept minimal: arbitrary possibly noncommutative division
rings and arbitrary finite linearly ordered index types, not `Field` or
`Fin n`. The generic sweep action formulas are reused directly; no
finite products are reopened.

Naturality under arbitrary `f : K →+* L` between division rings is proved
by combining sweep naturality with `f (a⁻¹) = (f a)⁻¹` for `a ≠ 0`.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {K : Type*} [DivisionRing K]

section RowClear

/-- Coefficients clearing column `c` above row `r` via left multiplication. -/
noncomputable def rowClearCoeffs (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) :
    RowIdx ι r → Multiplicative K :=
  fun i => (fun _ : M r c ≠ 0 => Multiplicative.ofAdd (-(M i.val c * (M r c)⁻¹))) hp

/-- Ambient `GL` element clearing column `c` above `r`. -/
noncomputable def rowClear (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) : GL ι K :=
  rowSweep r (rowClearCoeffs M r c hp)

/-- Restricted `U_ι(K)` element clearing column `c` above `r`. -/
noncomputable def _root_.Matrix.GeneralLinearGroup.UpperElementary.rowClear
    (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) :
    upperElementarySubgroup ι K :=
  UpperElementary.rowSweep r (rowClearCoeffs M r c hp)

@[simp]
theorem coe_upper_rowClear (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) :
    (↑(UpperElementary.rowClear M r c hp) : GL ι K) = rowClear M r c hp :=
  rfl

theorem rowClear_mul_apply (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0)
    (i j : ι) :
    (((rowClear M r c hp : GL ι K) : Matrix ι ι K) * M) i j =
      if i < r then M i j + (-(M i c * (M r c)⁻¹)) * M r j else M i j := by
  have h_gen := rowSweep_mul_apply (R := K) r (rowClearCoeffs M r c hp) M i j
  have h_eq : ((rowClear M r c hp : GL ι K) : Matrix ι ι K) =
      ((rowSweep r (rowClearCoeffs M r c hp) : GL ι K) : Matrix ι ι K) := rfl
  rw [← h_eq] at h_gen
  by_cases hi : i < r
  · have h_dite : (if h : i < r then
        M i j + (rowClearCoeffs M r c hp ⟨i, h⟩).toAdd * M r j else M i j) =
        M i j + (-(M i c * (M r c)⁻¹)) * M r j := by
      rw [dite_eq_left hi]
      simp [rowClearCoeffs]
    rw [h_dite] at h_gen
    rw [ite_eq_left hi]
    exact h_gen
  · have h_dite : (if h : i < r then
        M i j + (rowClearCoeffs M r c hp ⟨i, h⟩).toAdd * M r j else M i j) =
        M i j := by
      rw [dite_eq_right hi]
    rw [h_dite] at h_gen
    rw [ite_eq_right hi]
    exact h_gen

theorem rowClear_clears_above (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0)
    (i : ι) (hi : i < r) :
    (((rowClear M r c hp : GL ι K) : Matrix ι ι K) * M) i c = 0 := by
  have h := rowClear_mul_apply M r c hp i c
  rw [ite_eq_left hi] at h
  rw [h]
  have hp1 : (M r c)⁻¹ * M r c = 1 := inv_mul_cancel₀ hp
  have h_assoc : M i c * (M r c)⁻¹ * M r c = M i c := by
    rw [mul_assoc, hp1, mul_one]
  have h_neg : -(M i c * (M r c)⁻¹) * M r c = -(M i c * (M r c)⁻¹ * M r c) := by
    rw [neg_mul]
  rw [h_neg, h_assoc, add_neg_cancel]

theorem rowClear_row_r (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) (j : ι) :
    (((rowClear M r c hp : GL ι K) : Matrix ι ι K) * M) r j = M r j :=
  rowSweep_mul_apply_same_row (R := K) r _ M j

theorem rowClear_of_not_lt (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0)
    (i j : ι) (h : ¬(i < r)) :
    (((rowClear M r c hp : GL ι K) : Matrix ι ι K) * M) i j = M i j :=
  rowSweep_mul_apply_of_not_lt (R := K) r _ M i j h

end RowClear

section ColumnClear

/-- Coefficients clearing row `r` to the right of column `c`. -/
noncomputable def columnClearCoeffs (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) :
    ColIdx ι c → Multiplicative K :=
  fun j => (fun _ : M r c ≠ 0 => Multiplicative.ofAdd (-((M r c)⁻¹ * M r j.val))) hp

/-- Ambient `GL` element clearing row `r` to the right of `c`. -/
noncomputable def columnClear (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) : GL ι K :=
  columnSweep c (columnClearCoeffs M r c hp)

/-- Restricted `U_ι(K)` element clearing row `r` to the right of `c`. -/
noncomputable def _root_.Matrix.GeneralLinearGroup.UpperElementary.columnClear
    (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) :
    upperElementarySubgroup ι K :=
  UpperElementary.columnSweep c (columnClearCoeffs M r c hp)

@[simp]
theorem coe_upper_columnClear (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) :
    (↑(UpperElementary.columnClear M r c hp) : GL ι K) = columnClear M r c hp :=
  rfl

theorem columnClear_mul_apply (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0)
    (i j : ι) :
    (M * ((columnClear M r c hp : GL ι K) : Matrix ι ι K)) i j =
      if c < j then M i j + M i c * (-((M r c)⁻¹ * M r j)) else M i j := by
  have h_gen := columnSweep_mul_apply (R := K) c (columnClearCoeffs M r c hp) M i j
  have h_eq : ((columnClear M r c hp : GL ι K) : Matrix ι ι K) =
      ((columnSweep c (columnClearCoeffs M r c hp) : GL ι K) : Matrix ι ι K) := rfl
  rw [← h_eq] at h_gen
  by_cases hj : c < j
  · have h_dite : (if h : c < j then
        M i j + M i c * (columnClearCoeffs M r c hp ⟨j, h⟩).toAdd else M i j) =
        M i j + M i c * (-((M r c)⁻¹ * M r j)) := by
      rw [dite_eq_left hj]
      simp [columnClearCoeffs]
    rw [h_dite] at h_gen
    rw [ite_eq_left hj]
    exact h_gen
  · have h_dite : (if h : c < j then
        M i j + M i c * (columnClearCoeffs M r c hp ⟨j, h⟩).toAdd else M i j) =
        M i j := by
      rw [dite_eq_right hj]
    rw [h_dite] at h_gen
    rw [ite_eq_right hj]
    exact h_gen

theorem columnClear_clears_right (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0)
    (j : ι) (hj : c < j) :
    (M * ((columnClear M r c hp : GL ι K) : Matrix ι ι K)) r j = 0 := by
  have h := columnClear_mul_apply M r c hp r j
  rw [ite_eq_left hj] at h
  rw [h]
  have hp1 : M r c * (M r c)⁻¹ = 1 := mul_inv_cancel₀ hp
  have h_assoc : M r c * ((M r c)⁻¹ * M r j) = M r j := by
    rw [← mul_assoc, hp1, one_mul]
  have h_neg : M r c * -((M r c)⁻¹ * M r j) = -(M r c * ((M r c)⁻¹ * M r j)) := by
    rw [mul_neg]
  rw [h_neg, h_assoc, add_neg_cancel]

theorem columnClear_col_c (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) (i : ι) :
    (M * ((columnClear M r c hp : GL ι K) : Matrix ι ι K)) i c = M i c :=
  columnSweep_mul_apply_same_col (R := K) c _ M i

theorem columnClear_of_not_gt (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0)
    (i j : ι) (h : ¬(c < j)) :
    (M * ((columnClear M r c hp : GL ι K) : Matrix ι ι K)) i j = M i j :=
  columnSweep_mul_apply_of_not_gt (R := K) c _ M i j h

end ColumnClear

section PivotCleared

/-- Combined pivot-cleared matrix `L * M * R` where `L` clears above and `R` clears to the right. -/
noncomputable def pivotCleared (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) :
    Matrix ι ι K :=
  ((rowClear M r c hp : GL ι K) : Matrix ι ι K) * M *
    ((columnClear M r c hp : GL ι K) : Matrix ι ι K)

theorem pivotCleared_pivot (M : Matrix ι ι K) (r c : ι) (hp : M r c ≠ 0) :
    pivotCleared M r c hp r c = M r c := by
  unfold pivotCleared
  have h_same_col : ∀ (N : Matrix ι ι K),
      (N * ((columnClear M r c hp : GL ι K) : Matrix ι ι K)) r c = N r c := by
    intro N
    exact columnSweep_mul_apply_same_col (R := K) c (columnClearCoeffs M r c hp) N r
  rw [h_same_col]
  exact rowClear_row_r M r c hp c

end PivotCleared

section GreatestHelpers

omit [DecidableEq ι] [Fintype ι] in
theorem isGreatest_support_iff (M : Matrix ι ι K) (r c : ι) :
    IsGreatest {i | M i c ≠ 0} r ↔ M r c ≠ 0 ∧ ∀ i, r < i → M i c = 0 := by
  constructor
  · intro hg
    constructor
    · exact hg.1
    · intro i hri
      by_contra h
      have hi_mem : i ∈ {i | M i c ≠ 0} := h
      have hle := hg.2 hi_mem
      have h_lt : r < r := lt_of_lt_of_le hri hle
      exact lt_irrefl r h_lt
  · intro ⟨hr, hvan⟩
    constructor
    · exact hr
    · intro i hi
      by_contra h_not_le
      have hlt : r < i := not_le.mp h_not_le
      exact hi (hvan i hlt)

omit [DecidableEq ι] [Fintype ι] in
theorem isGreatest_support_imp_gt_eq_zero {M : Matrix ι ι K} {r c : ι}
    (hg : IsGreatest {i | M i c ≠ 0} r) (i : ι) (hi : r < i) : M i c = 0 :=
  ((isGreatest_support_iff M r c).mp hg).2 i hi

omit [DecidableEq ι] [Fintype ι] in
theorem isGreatest_support_imp_mem {M : Matrix ι ι K} {r c : ι}
    (hg : IsGreatest {i | M i c ≠ 0} r) : M r c ≠ 0 :=
  ((isGreatest_support_iff M r c).mp hg).1

end GreatestHelpers

section LeastHelpers

omit [DecidableEq ι] [Fintype ι] K in
theorem isLeast_univ_iff_forall_le (c : ι) :
    IsLeast (Set.univ : Set ι) c ↔ ∀ j : ι, c ≤ j := by
  constructor
  · intro h j
    exact h.2 (Set.mem_univ j)
  · intro h
    exact ⟨Set.mem_univ c, fun _ _ => h _⟩

omit [DecidableEq ι] [Fintype ι] K in
theorem isLeast_univ_imp_lt_of_ne {c j : ι} (hc : IsLeast (Set.univ : Set ι) c)
    (hj : j ≠ c) : c < j := by
  have hle : c ≤ j := (isLeast_univ_iff_forall_le c).mp hc j
  have h_ne : c ≠ j := Ne.symm hj
  exact lt_of_le_of_ne hle h_ne

omit [DecidableEq ι] [Fintype ι] K in
theorem isLeast_univ_imp_forall_le {c : ι} (hc : IsLeast (Set.univ : Set ι) c)
    (j : ι) : c ≤ j :=
  ((isLeast_univ_iff_forall_le c).mp hc) j

end LeastHelpers

section ColRowIsolated

theorem rowClear_col_isolated_of_isGreatest {M : Matrix ι ι K} {r c : ι}
    (hp : M r c ≠ 0) (hg : IsGreatest {i | M i c ≠ 0} r) (i : ι) :
    (((rowClear M r c hp : GL ι K) : Matrix ι ι K) * M) i c =
      if i = r then M r c else 0 := by
  by_cases hir : i = r
  · rw [ite_eq_left hir, hir, rowClear_row_r]
  · rw [ite_eq_right hir]
    by_cases hlt : i < r
    · rw [rowClear_clears_above M r c hp i hlt]
    · have hgt : r < i := by
        have h_le : r ≤ i := le_of_not_gt hlt
        have h_ne : r ≠ i := Ne.symm hir
        exact lt_of_le_of_ne h_le h_ne
      have h_zero : M i c = 0 := isGreatest_support_imp_gt_eq_zero hg i hgt
      have h_eq := rowClear_of_not_lt M r c hp i c hlt
      rw [h_eq, h_zero]

theorem pivotCleared_col_isolated {M : Matrix ι ι K} {r c : ι}
    (hp : M r c ≠ 0) (hg : IsGreatest {i | M i c ≠ 0} r) (i : ι) :
    pivotCleared M r c hp i c = if i = r then M r c else 0 := by
  unfold pivotCleared
  have h_same_col : ∀ (N : Matrix ι ι K),
      (N * ((columnClear M r c hp : GL ι K) : Matrix ι ι K)) i c = N i c := by
    intro N
    exact columnSweep_mul_apply_same_col (R := K) c (columnClearCoeffs M r c hp) N i
  rw [h_same_col]
  exact rowClear_col_isolated_of_isGreatest hp hg i

theorem columnClear_row_isolated_of_isLeast {M : Matrix ι ι K} {r c : ι}
    (hp : M r c ≠ 0) (hc : IsLeast (Set.univ : Set ι) c) (j : ι) :
    (M * ((columnClear M r c hp : GL ι K) : Matrix ι ι K)) r j =
      if j = c then M r c else 0 := by
  by_cases hjc : j = c
  · rw [ite_eq_left hjc, hjc, columnClear_col_c]
  · rw [ite_eq_right hjc]
    have hlt : c < j := isLeast_univ_imp_lt_of_ne hc hjc
    exact columnClear_clears_right M r c hp j hlt

theorem pivotCleared_row_isolated {M : Matrix ι ι K} {r c : ι}
    (hp : M r c ≠ 0) (hc : IsLeast (Set.univ : Set ι) c) (j : ι) :
    pivotCleared M r c hp r j = if j = c then M r c else 0 := by
  have h_row_r : ∀ j',
      (((rowClear M r c hp : GL ι K) : Matrix ι ι K) * M) r j' = M r j' := by
    intro j'
    exact rowClear_row_r M r c hp j'
  calc pivotCleared M r c hp r j
      = ((rowClear M r c hp : GL ι K) * M * (columnClear M r c hp : GL ι K) :
          Matrix ι ι K) r j := rfl
    _ = ∑ k, (((rowClear M r c hp : GL ι K) : Matrix ι ι K) * M) r k *
          ((columnClear M r c hp : GL ι K) : Matrix ι ι K) k j := by
        simp [Matrix.mul_apply]
    _ = ∑ k, M r k * ((columnClear M r c hp : GL ι K) : Matrix ι ι K) k j := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h_row_r]
    _ = (M * ((columnClear M r c hp : GL ι K) : Matrix ι ι K)) r j := by
        simp [Matrix.mul_apply]
    _ = if j = c then M r c else 0 := columnClear_row_isolated_of_isLeast hp hc j

theorem pivotCleared_row_isolated_of_forall_le {M : Matrix ι ι K} {r c : ι}
    (hp : M r c ≠ 0) (hc : ∀ j : ι, c ≤ j) (j : ι) :
    pivotCleared M r c hp r j = if j = c then M r c else 0 := by
  have hc' : IsLeast (Set.univ : Set ι) c := (isLeast_univ_iff_forall_le c).mpr hc
  exact pivotCleared_row_isolated hp hc' j

end ColRowIsolated

section Naturality

variable {L : Type*} [DivisionRing L]

private theorem ringHom_map_ne_zero {f : K →+* L} {a : K} (ha : a ≠ 0) :
    f a ≠ 0 := by
  intro h_zero
  have h_one : f 1 = 1 := f.map_one
  have h_a_inv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have h_mul : f a * f a⁻¹ = 1 := by
    calc f a * f a⁻¹ = f (a * a⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [h_a_inv]
      _ = 1 := h_one
  rw [h_zero, zero_mul] at h_mul
  exact one_ne_zero h_mul.symm

private theorem ringHom_map_inv {f : K →+* L} {a : K} (ha : a ≠ 0) :
    f a⁻¹ = (f a)⁻¹ := by
  have hfa_ne : f a ≠ 0 := ringHom_map_ne_zero ha
  have h1 : f a * f a⁻¹ = 1 := by
    have : f (a * a⁻¹) = f 1 := by rw [mul_inv_cancel₀ ha]
    calc f a * f a⁻¹ = f (a * a⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [this]
      _ = 1 := f.map_one
  have h2 : (f a)⁻¹ * f a = 1 := inv_mul_cancel₀ hfa_ne
  calc f a⁻¹ = 1 * f a⁻¹ := by rw [one_mul]
    _ = ((f a)⁻¹ * f a) * f a⁻¹ := by rw [h2]
    _ = (f a)⁻¹ * (f a * f a⁻¹) := by rw [mul_assoc]
    _ = (f a)⁻¹ * 1 := by rw [h1]
    _ = (f a)⁻¹ := by rw [mul_one]

omit [DecidableEq ι] [Fintype ι] in
theorem rowClearCoeffs_map (f : K →+* L) (M : Matrix ι ι K) (r c : ι)
    (hp : M r c ≠ 0) (hp' : (M.map ⇑f) r c ≠ 0) (i : RowIdx ι r) :
    multiplicativeMap f (rowClearCoeffs M r c hp i) =
      rowClearCoeffs (M.map ⇑f) r c hp' i := by
  simp only [rowClearCoeffs, multiplicativeMap]
  have h1 : f (M i.val c) = (M.map ⇑f) i.val c := rfl
  have h2 : f (M r c) = (M.map ⇑f) r c := rfl
  calc f (-(M i.val c * (M r c)⁻¹))
      = -(f (M i.val c * (M r c)⁻¹)) := by rw [f.map_neg]
    _ = -(f (M i.val c) * f ((M r c)⁻¹)) := by rw [f.map_mul]
    _ = -(f (M i.val c) * (f (M r c))⁻¹) := by rw [ringHom_map_inv hp]
    _ = -((M.map ⇑f) i.val c * ((M.map ⇑f) r c)⁻¹) := by rw [h1, h2]

theorem rowClear_mapRingHom (f : K →+* L) (M : Matrix ι ι K) (r c : ι)
    (hp : M r c ≠ 0) (hp' : (M.map ⇑f) r c ≠ 0) :
    mapRingHom (n := ι) f (rowClear M r c hp) =
      rowClear (M.map ⇑f) r c hp' := by
  unfold rowClear
  rw [rowSweep_mapRingHom (f := f) (r := r)]
  congr 1
  funext i
  exact rowClearCoeffs_map f M r c hp hp' i

theorem upperRowClear_mapRingHom (f : K →+* L) (M : Matrix ι ι K) (r c : ι)
    (hp : M r c ≠ 0) (hp' : (M.map ⇑f) r c ≠ 0) :
    UpperElementary.mapRingHom (ι := ι) f (UpperElementary.rowClear M r c hp) =
      UpperElementary.rowClear (M.map ⇑f) r c hp' := by
  apply Subtype.ext
  simp only [UpperElementary.coe_mapRingHom]
  exact rowClear_mapRingHom f M r c hp hp'

omit [DecidableEq ι] [Fintype ι] in
theorem columnClearCoeffs_map (f : K →+* L) (M : Matrix ι ι K) (r c : ι)
    (hp : M r c ≠ 0) (hp' : (M.map ⇑f) r c ≠ 0) (j : ColIdx ι c) :
    multiplicativeMap f (columnClearCoeffs M r c hp j) =
      columnClearCoeffs (M.map ⇑f) r c hp' j := by
  simp only [columnClearCoeffs, multiplicativeMap]
  have h1 : f (M r j.val) = (M.map ⇑f) r j.val := rfl
  have h2 : f (M r c) = (M.map ⇑f) r c := rfl
  calc Multiplicative.ofAdd (f (-((M r c)⁻¹ * M r j.val)))
      = Multiplicative.ofAdd (-(f ((M r c)⁻¹ * M r j.val))) := by rw [f.map_neg]
    _ = Multiplicative.ofAdd (-(f ((M r c)⁻¹) * f (M r j.val))) := by rw [f.map_mul]
    _ = Multiplicative.ofAdd (-((f (M r c))⁻¹ * f (M r j.val))) := by
        rw [ringHom_map_inv hp]
    _ = Multiplicative.ofAdd (-(((M.map ⇑f) r c)⁻¹ * (M.map ⇑f) r j.val)) := by
        rw [h1, h2]

theorem columnClear_mapRingHom (f : K →+* L) (M : Matrix ι ι K) (r c : ι)
    (hp : M r c ≠ 0) (hp' : (M.map ⇑f) r c ≠ 0) :
    mapRingHom (n := ι) f (columnClear M r c hp) =
      columnClear (M.map ⇑f) r c hp' := by
  unfold columnClear
  rw [columnSweep_mapRingHom (f := f) (c := c)]
  congr 1
  funext j
  exact columnClearCoeffs_map f M r c hp hp' j

theorem upperColumnClear_mapRingHom (f : K →+* L) (M : Matrix ι ι K) (r c : ι)
    (hp : M r c ≠ 0) (hp' : (M.map ⇑f) r c ≠ 0) :
    UpperElementary.mapRingHom (ι := ι) f (UpperElementary.columnClear M r c hp) =
      UpperElementary.columnClear (M.map ⇑f) r c hp' := by
  apply Subtype.ext
  simp only [UpperElementary.coe_mapRingHom]
  exact columnClear_mapRingHom f M r c hp hp'

omit [DecidableEq ι] [LinearOrder ι] in
private theorem matrix_map_mul (f : K →+* L) (A B : Matrix ι ι K) :
    (A * B).map ⇑f = A.map ⇑f * B.map ⇑f := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [f.map_mul]

omit [DecidableEq ι] [LinearOrder ι] in
private theorem matrix_map_mul_assoc (f : K →+* L) (A B C : Matrix ι ι K) :
    (A * B * C).map ⇑f = A.map ⇑f * B.map ⇑f * C.map ⇑f := by
  calc (A * B * C).map ⇑f = ((A * B) * C).map ⇑f := by rfl
    _ = (A * B).map ⇑f * C.map ⇑f := matrix_map_mul f (A * B) C
    _ = (A.map ⇑f * B.map ⇑f) * C.map ⇑f := by rw [matrix_map_mul f A B]
    _ = A.map ⇑f * B.map ⇑f * C.map ⇑f := by rw [Matrix.mul_assoc]

theorem pivotCleared_map (f : K →+* L) (M : Matrix ι ι K) (r c : ι)
    (hp : M r c ≠ 0) (hp' : (M.map ⇑f) r c ≠ 0) :
    (pivotCleared M r c hp).map ⇑f = pivotCleared (M.map ⇑f) r c hp' := by
  unfold pivotCleared
  have hL : ((rowClear M r c hp : GL ι K) : Matrix ι ι K).map ⇑f =
      ((rowClear (M.map ⇑f) r c hp' : GL ι L) : Matrix ι ι L) := by
    calc ((rowClear M r c hp : GL ι K) : Matrix ι ι K).map ⇑f
        = ((mapRingHom (n := ι) f (rowClear M r c hp) : GL ι L) : Matrix ι ι L) := by
          rw [coe_mapRingHom]
      _ = ((rowClear (M.map ⇑f) r c hp' : GL ι L) : Matrix ι ι L) := by
          rw [rowClear_mapRingHom f M r c hp hp']
  have hR : ((columnClear M r c hp : GL ι K) : Matrix ι ι K).map ⇑f =
      ((columnClear (M.map ⇑f) r c hp' : GL ι L) : Matrix ι ι L) := by
    calc ((columnClear M r c hp : GL ι K) : Matrix ι ι K).map ⇑f
        = ((mapRingHom (n := ι) f (columnClear M r c hp) : GL ι L) : Matrix ι ι L) := by
          rw [coe_mapRingHom]
      _ = ((columnClear (M.map ⇑f) r c hp' : GL ι L) : Matrix ι ι L) := by
          rw [columnClear_mapRingHom f M r c hp hp']
  have h_eq := matrix_map_mul_assoc f
    ((rowClear M r c hp : GL ι K) : Matrix ι ι K) M
    ((columnClear M r c hp : GL ι K) : Matrix ι ι K)
  rw [h_eq, hL, hR]

end Naturality

end Matrix.GeneralLinearGroup
