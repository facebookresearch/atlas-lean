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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.HeterogeneousIsolatedEntry
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.UpperElementaryRectangular
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.CanonicalPivotReduction
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.HeterogeneousBruhatInsertion

/-!
# Pivot reduction for rectangular matrices
-/

@[expose] public section

namespace Matrix

namespace GeneralLinearEquiv

open Matrix.GeneralLinearGroup

/-! ### A. Rectangular chosen-pivot clearing -/

section RowClearCoeffs

variable {m n : Type*} [LinearOrder m]
variable {K : Type*} [DivisionRing K]

/-- Row-clear coefficients `-(M i c * (M r c)⁻¹)` for `M : Matrix m n K`. -/
noncomputable def rowClearCoeffs (M : Matrix m n K) (r : m) (c : n)
    (_hp : M r c ≠ 0) : RowIdx m r → Multiplicative K :=
  fun i => Multiplicative.ofAdd (-(M i.val c * (M r c)⁻¹))

end RowClearCoeffs

section RowClearDef

variable {m : Type*} [DecidableEq m] [Fintype m] [LinearOrder m]
variable {n : Type*}
variable {K : Type*} [DivisionRing K]

/-- For a nonzero pivot `M r c` over a division ring, the left factor
`L ∈ GL m K` clears column `c` above `r`. -/
noncomputable def rowClear (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) : GL m K :=
  Matrix.GeneralLinearGroup.rowSweep r (rowClearCoeffs M r c hp)

/-- Restricted `U_m(K)` left factor. -/
noncomputable def upperRowClear (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) : upperElementarySubgroup m K :=
  UpperElementary.rowSweep r (rowClearCoeffs M r c hp)

@[simp]
theorem coe_upperRowClear (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) :
    (↑(upperRowClear M r c hp) : GL m K) = rowClear M r c hp :=
  rfl

end RowClearDef

section RowClearLemmas

variable {m : Type*} [DecidableEq m] [Fintype m] [LinearOrder m]
variable {n : Type*}
variable {K : Type*} [DivisionRing K]

theorem rowClear_mul_apply (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) (j : n) :
    (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i j =
      if i < r then M i j + (-(M i c * (M r c)⁻¹)) * M r j else M i j := by
  have hRect := Matrix.GeneralLinearGroup.rowSweep_mul_apply_rect (R := K) (κ := n)
    (r := r) (v := rowClearCoeffs M r c hp) (M := M) (i := i) (j := j)
  have hLHS : (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i j =
      (((Matrix.GeneralLinearGroup.rowSweep r (rowClearCoeffs M r c hp) : GL m K) :
        Matrix m m K) * M) i j := rfl
  rw [hLHS, hRect]
  by_cases hi : i < r
  · rw [dite_eq_left hi, ite_eq_left hi]
    simp [rowClearCoeffs]
  · rw [dite_eq_right hi, ite_eq_right hi]

theorem rowClear_clears_above (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) (hi : i < r) :
    (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i c = 0 := by
  have h := rowClear_mul_apply M r c hp i c
  rw [ite_eq_left hi] at h
  rw [h]
  have hp1 : (M r c)⁻¹ * M r c = 1 := inv_mul_cancel₀ hp
  have hAssoc : M i c * (M r c)⁻¹ * M r c = M i c := by
    calc M i c * (M r c)⁻¹ * M r c
        = M i c * ((M r c)⁻¹ * M r c) := by rw [mul_assoc]
      _ = M i c * 1 := by rw [hp1]
      _ = M i c := by rw [mul_one]
  have hNeg : -(M i c * (M r c)⁻¹) * M r c =
      -(M i c * (M r c)⁻¹ * M r c) := by
    rw [neg_mul]
  rw [hNeg, hAssoc, add_neg_cancel]

theorem rowClear_preserves_row (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (j : n) :
    (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r j = M r j := by
  exact Matrix.GeneralLinearGroup.rowSweep_mul_apply_same_row_rect (R := K) (κ := n)
    (r := r) (v := rowClearCoeffs M r c hp) (M := M) (j := j)

theorem rowClear_of_not_lt (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) (j : n) (h : ¬(i < r)) :
    (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i j = M i j := by
  exact Matrix.GeneralLinearGroup.rowSweep_mul_apply_of_not_lt_rect (R := K) (κ := n)
    (r := r) (v := rowClearCoeffs M r c hp) (M := M) (i := i) (j := j) h

theorem pivotClearedMatrix_LM (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) (k : n) :
    (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i k =
      if i < r then M i k + (-(M i c * (M r c)⁻¹)) * M r k else M i k := by
  exact rowClear_mul_apply M r c hp i k

theorem pivotClearedMatrix_LM_col_c (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) :
    (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i c =
      if i < r then 0 else M i c := by
  by_cases hi : i < r
  · rw [ite_eq_left hi, rowClear_clears_above M r c hp i hi]
  · rw [ite_eq_right hi, rowClear_of_not_lt M r c hp i c hi]

end RowClearLemmas

section ColClearCoeffs

variable {m n : Type*} [LinearOrder n]
variable {K : Type*} [DivisionRing K]

/-- Column-clear coefficients `-((M r c)⁻¹ * M r j)` for `M : Matrix m n K`. -/
noncomputable def columnClearCoeffs (M : Matrix m n K) (r : m) (c : n)
    (_hp : M r c ≠ 0) : ColIdx n c → Multiplicative K :=
  fun j => Multiplicative.ofAdd (-((M r c)⁻¹ * M r j.val))

end ColClearCoeffs

section ColClearDef

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]
variable {m : Type*}
variable {K : Type*} [DivisionRing K]

/-- For a nonzero pivot `M r c` over a division ring, the right factor
`R ∈ GL n K` clears row `r` to the right of `c`. -/
noncomputable def columnClear (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) : GL n K :=
  Matrix.GeneralLinearGroup.columnSweep c (columnClearCoeffs M r c hp)

/-- Restricted `U_n(K)` right factor. -/
noncomputable def upperColumnClear (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) : upperElementarySubgroup n K :=
  UpperElementary.columnSweep c (columnClearCoeffs M r c hp)

@[simp]
theorem coe_upperColumnClear (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) :
    (↑(upperColumnClear M r c hp) : GL n K) = columnClear M r c hp :=
  rfl

end ColClearDef

section ColClearLemmas

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]
variable {m : Type*}
variable {K : Type*} [DivisionRing K]

theorem columnClear_mul_apply (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) (j : n) :
    (M * ((columnClear M r c hp : GL n K) : Matrix n n K)) i j =
      if c < j then M i j + M i c * (-((M r c)⁻¹ * M r j)) else M i j := by
  have hRect := Matrix.GeneralLinearGroup.columnSweep_mul_apply_rect (R := K) (κ := m)
    (c := c) (v := columnClearCoeffs M r c hp) (M := M) (i := i) (j := j)
  have hLHS : (M * ((columnClear M r c hp : GL n K) : Matrix n n K)) i j =
      (M * ((Matrix.GeneralLinearGroup.columnSweep c (columnClearCoeffs M r c hp) :
        GL n K) : Matrix n n K)) i j := rfl
  rw [hLHS, hRect]
  by_cases hj : c < j
  · rw [dite_eq_left hj, ite_eq_left hj]
    simp [columnClearCoeffs]
  · rw [dite_eq_right hj, ite_eq_right hj]

theorem columnClear_clears_right (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (j : n) (hj : c < j) :
    (M * ((columnClear M r c hp : GL n K) : Matrix n n K)) r j = 0 := by
  have h := columnClear_mul_apply M r c hp r j
  rw [ite_eq_left hj] at h
  rw [h]
  have hp1 : M r c * (M r c)⁻¹ = 1 := mul_inv_cancel₀ hp
  have hAssoc : M r c * ((M r c)⁻¹ * M r j) = M r j := by
    calc M r c * ((M r c)⁻¹ * M r j)
        = M r c * (M r c)⁻¹ * M r j := by rw [← mul_assoc]
      _ = 1 * M r j := by rw [hp1]
      _ = M r j := by rw [one_mul]
  have hNeg : M r c * -((M r c)⁻¹ * M r j) =
      -(M r c * ((M r c)⁻¹ * M r j)) := by
    rw [mul_neg]
  rw [hNeg, hAssoc, add_neg_cancel]

theorem columnClear_preserves_col (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) :
    (M * ((columnClear M r c hp : GL n K) : Matrix n n K)) i c = M i c := by
  exact Matrix.GeneralLinearGroup.columnSweep_mul_apply_same_col_rect (R := K) (κ := m)
    (c := c) (v := columnClearCoeffs M r c hp) (M := M) (i := i)

theorem columnClear_of_not_gt (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) (j : n) (h : ¬(c < j)) :
    (M * ((columnClear M r c hp : GL n K) : Matrix n n K)) i j = M i j := by
  exact Matrix.GeneralLinearGroup.columnSweep_mul_apply_of_not_gt_rect (R := K) (κ := m)
    (c := c) (v := columnClearCoeffs M r c hp) (M := M) (i := i) (j := j) h

end ColClearLemmas

section PivotClearedDef

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

/-- Pivot-cleared matrix `L * M * R` for rectangular `M`. -/
noncomputable def pivotClearedMatrix (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) : Matrix m n K :=
  ((rowClear M r c hp : GL m K) : Matrix m m K) * M *
    ((columnClear M r c hp : GL n K) : Matrix n n K)

theorem pivotClearedMatrix_pivot (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) :
    pivotClearedMatrix M r c hp r c = M r c := by
  unfold pivotClearedMatrix
  have hCol : ∀ (N : Matrix m n K),
      (N * ((columnClear M r c hp : GL n K) : Matrix n n K)) r c = N r c := by
    intro N
    exact Matrix.GeneralLinearGroup.columnSweep_mul_apply_same_col_rect (R := K) (κ := m)
      (c := c) (v := columnClearCoeffs M r c hp) (M := N) (i := r)
  calc ((((rowClear M r c hp : GL m K) : Matrix m m K) * M *
        ((columnClear M r c hp : GL n K) : Matrix n n K) : Matrix m n K) r c)
      = ((((rowClear M r c hp : GL m K) : Matrix m m K) * M) r c) :=
        hCol (((rowClear M r c hp : GL m K) : Matrix m m K) * M)
    _ = M r c := by rw [rowClear_preserves_row]

theorem pivotClearedMatrix_apply_general (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (i : m) (j : n) :
    pivotClearedMatrix M r c hp i j =
      let LMij := if i < r then M i j + (-(M i c * (M r c)⁻¹)) * M r j else M i j
      let LMic := if i < r then (0 : K) else M i c
      if c < j then LMij + LMic * (-((M r c)⁻¹ * M r j)) else LMij := by
  unfold pivotClearedMatrix
  have hLM : ∀ k : n,
      (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i k =
        if i < r then M i k + (-(M i c * (M r c)⁻¹)) * M r k else M i k := by
    intro k
    exact rowClear_mul_apply M r c hp i k
  have hLMC : (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i c =
      if i < r then (0 : K) else M i c := by
    by_cases hi : i < r
    · rw [ite_eq_left hi, rowClear_clears_above M r c hp i hi]
    · rw [ite_eq_right hi, rowClear_of_not_lt M r c hp i c hi]
  have hpLM : (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r c ≠ 0 := by
    rw [rowClear_preserves_row M r c hp]
    exact hp
  have hCoeffEq : columnClear M r c hp =
      columnClear (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r c hpLM := by
    apply congrArg (Matrix.GeneralLinearGroup.columnSweep c)
    funext j
    simp only [columnClearCoeffs]
    have h1 : (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r c = M r c :=
      rowClear_preserves_row M r c hp c
    have h2 : (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r j.val = M r j.val :=
      rowClear_preserves_row M r c hp j.val
    rw [h1, h2]
  calc ((((rowClear M r c hp : GL m K) : Matrix m m K) * M *
        ((columnClear M r c hp : GL n K) : Matrix n n K) : Matrix m n K) i j)
      = ((((rowClear M r c hp : GL m K) : Matrix m m K) * M *
        ((columnClear (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r c hpLM :
          GL n K) : Matrix n n K) : Matrix m n K) i j) := by
        rw [hCoeffEq]
      _ = if c < j then
          (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i j +
          (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i c *
            (-((M r c)⁻¹ * M r j))
        else
          (((rowClear M r c hp : GL m K) : Matrix m m K) * M) i j := by
        have h := columnClear_mul_apply
          (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r c hpLM i j
        have h1 : (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r c = M r c :=
          rowClear_preserves_row M r c hp c
        have h2 : (((rowClear M r c hp : GL m K) : Matrix m m K) * M) r j = M r j :=
          rowClear_preserves_row M r c hp j
        rw [h1, h2] at h
        exact h
      _ = if c < j then
          (if i < r then M i j + (-(M i c * (M r c)⁻¹)) * M r j else M i j) +
          (if i < r then (0 : K) else M i c) * (-((M r c)⁻¹ * M r j))
        else
          if i < r then M i j + (-(M i c * (M r c)⁻¹)) * M r j else M i j := by
        rw [hLM j, hLMC]

theorem pivotClearedMatrix_congr_row (M : Matrix m n K) (r r' : m) (c : n)
    (hp : M r c ≠ 0) (hp' : M r' c ≠ 0) (h : r' = r) (i : m) (j : n) :
    pivotClearedMatrix M r c hp i j = pivotClearedMatrix M r' c hp' i j := by
  subst h
  rfl

theorem pivotClearedMatrix_eq_of_row_eq (M : Matrix m n K) (r r' : m) (c : n)
    (hp : M r c ≠ 0) (hp' : M r' c ≠ 0) (h : r' = r) :
    pivotClearedMatrix M r c hp = pivotClearedMatrix M r' c hp' := by
  ext i j
  exact pivotClearedMatrix_congr_row M r r' c hp hp' h i j

end PivotClearedDef

/-! ### B. Chosen-pivot heterogeneous equivalence -/

section IsGreatestLem

variable {ι : Type*} [LinearOrder ι]
variable {κ : Type*}
variable {K : Type*} [DivisionRing K]

theorem isGreatest_iff_ne_zero_and_forall_gt_eq_zero
    (M : Matrix ι κ K) (rr : ι) (cc : κ) :
    IsGreatest {i | M i cc ≠ 0} rr ↔ M rr cc ≠ 0 ∧ ∀ i, rr < i → M i cc = 0 := by
  constructor
  · intro hg
    constructor
    · exact hg.1
    · intro i hri
      by_contra h
      have hiMem : i ∈ {i | M i cc ≠ 0} := h
      have hle := hg.2 hiMem
      have hlt : rr < rr := lt_of_lt_of_le hri hle
      exact lt_irrefl rr hlt
  · intro ⟨hr, hvan⟩
    constructor
    · exact hr
    · intro i hi
      by_contra hNotLe
      have hlt : rr < i := not_le.mp hNotLe
      exact hi (hvan i hlt)

end IsGreatestLem

section LeftCleared

variable {m : Type*} [DecidableEq m] [Fintype m] [LinearOrder m]
variable {n : Type*} [DecidableEq n] [Fintype n]
variable {K : Type*} [DivisionRing K]

/-- Left-cleared heterogeneous equivalence `ofGL L ⬝ e`. -/
noncomputable def leftClearedEquiv (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) : GeneralLinearEquiv m n K :=
  (GeneralLinearEquiv.ofGL (rowClear e.val r c hp)).trans e

/-- Exposed left upper-elementary factor. -/
noncomputable def leftUpperFactor (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) : upperElementarySubgroup m K :=
  upperRowClear e.val r c hp

theorem val_leftClearedEquiv (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) :
    (leftClearedEquiv e r c hp).val =
      ((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val := rfl

@[simp]
theorem coe_leftUpperFactor (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) :
    (↑(leftUpperFactor e r c hp) : GL m K) = rowClear e.val r c hp :=
  rfl

end LeftCleared

section RightCleared

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]
variable {m : Type*} [DecidableEq m] [Fintype m]
variable {K : Type*} [DivisionRing K]

/-- Exposed right upper-elementary factor. -/
noncomputable def rightUpperFactor (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) : upperElementarySubgroup n K :=
  upperColumnClear e.val r c hp

@[simp]
theorem coe_rightUpperFactor (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) :
    (↑(rightUpperFactor e r c hp) : GL n K) = columnClear e.val r c hp :=
  rfl

end RightCleared

section PivotBoth

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

/-- Right-cleared heterogeneous equivalence `ofGL L ⬝ e ⬝ ofGL R`. -/
noncomputable def pivotClearedEquiv (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) : GeneralLinearEquiv m n K :=
  ((GeneralLinearEquiv.ofGL (rowClear e.val r c hp)).trans e).trans
    (GeneralLinearEquiv.ofGL (columnClear e.val r c hp))

theorem val_pivotClearedEquiv (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) :
    (pivotClearedEquiv e r c hp).val =
      ((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val *
        ((columnClear e.val r c hp : GL n K) : Matrix n n K) := rfl

theorem val_pivotClearedEquiv_eq_matrix (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) :
    (pivotClearedEquiv e r c hp).val = pivotClearedMatrix e.val r c hp := rfl

theorem pivotClearedEquiv_pivot (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) :
    (pivotClearedEquiv e r c hp).val r c = e.val r c := by
  rw [val_pivotClearedEquiv_eq_matrix, pivotClearedMatrix_pivot]

theorem pivotClearedEquiv_col_isolated_of_isGreatest
    (e : GeneralLinearEquiv m n K) (r : m) (c : n) (hp : e.val r c ≠ 0)
    (hg : IsGreatest {i | e.val i c ≠ 0} r) (i : m) :
    (pivotClearedEquiv e r c hp).val i c = if i = r then e.val r c else 0 := by
  have hg' : ∀ k : m, r < k → e.val k c = 0 := by
    intro k hk
    exact ((isGreatest_iff_ne_zero_and_forall_gt_eq_zero e.val r c).mp hg).2 k hk
  have hRow : ∀ i' : m,
      (((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) i' c =
        if i' = r then e.val r c else 0 := by
    intro i'
    by_cases hir : i' = r
    · rw [ite_eq_left hir, hir, rowClear_preserves_row]
    · rw [ite_eq_right hir]
      by_cases hlt : i' < r
      · exact rowClear_clears_above e.val r c hp i' hlt
      · have hgt : r < i' := by
          have hLe : r ≤ i' := le_of_not_gt hlt
          exact lt_of_le_of_ne hLe (Ne.symm hir)
        calc (((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) i' c
            = e.val i' c := rowClear_of_not_lt e.val r c hp i' c hlt
          _ = 0 := hg' i' hgt
  calc (pivotClearedEquiv e r c hp).val i c
      = ((((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) *
          ((columnClear e.val r c hp : GL n K) : Matrix n n K)) i c := by
          rw [val_pivotClearedEquiv]
    _ = (((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) i c := by
          exact Matrix.GeneralLinearGroup.columnSweep_mul_apply_same_col_rect
            (R := K) (κ := m) (c := c)
            (v := columnClearCoeffs e.val r c hp)
            (M := ((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val)
            (i := i)
    _ = if i = r then e.val r c else 0 := hRow i

theorem pivotClearedEquiv_row_isolated_of_isLeast
    (e : GeneralLinearEquiv m n K) (r : m) (c : n) (hp : e.val r c ≠ 0)
    (hc : IsLeast (Set.univ : Set n) c) (j : n) :
    (pivotClearedEquiv e r c hp).val r j = if j = c then e.val r c else 0 := by
  have hRowR : ∀ j',
      (((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) r j' = e.val r j' :=
    fun j' => rowClear_preserves_row e.val r c hp j'
  have hcLen : ∀ k : n, c ≤ k := fun k => hc.2 (Set.mem_univ k)
  by_cases hjc : j = c
  · rw [ite_eq_left hjc, hjc]
    calc (pivotClearedEquiv e r c hp).val r c
        = ((((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) *
            ((columnClear e.val r c hp : GL n K) : Matrix n n K)) r c := by
            rw [val_pivotClearedEquiv]
      _ = (((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) r c := by
            exact Matrix.GeneralLinearGroup.columnSweep_mul_apply_same_col_rect
              (R := K) (κ := m) (c := c)
              (v := columnClearCoeffs e.val r c hp)
              (M := ((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val)
              (i := r)
      _ = e.val r c := hRowR c
  · rw [ite_eq_right hjc]
    have hlt : c < j := lt_of_le_of_ne (hcLen j) (Ne.symm hjc)
    calc (pivotClearedEquiv e r c hp).val r j
        = ((((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) *
            ((columnClear e.val r c hp : GL n K) : Matrix n n K)) r j := by
            rw [val_pivotClearedEquiv]
      _ = ∑ k : n,
            (((rowClear e.val r c hp : GL m K) : Matrix m m K) * e.val) r k *
              ((columnClear e.val r c hp : GL n K) : Matrix n n K) k j := by
            simp [Matrix.mul_apply]
      _ = ∑ k : n,
            e.val r k * ((columnClear e.val r c hp : GL n K) : Matrix n n K) k j := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hRowR k]
      _ = (e.val * ((columnClear e.val r c hp : GL n K) : Matrix n n K)) r j := by
            simp [Matrix.mul_apply]
      _ = 0 := by
            have hm := columnClear_mul_apply e.val r c hp r j
            rw [ite_eq_left hlt] at hm
            rw [hm]
            have hp1 : e.val r c * (e.val r c)⁻¹ = 1 := mul_inv_cancel₀ hp
            have hAssoc : e.val r c * ((e.val r c)⁻¹ * e.val r j) = e.val r j := by
              calc e.val r c * ((e.val r c)⁻¹ * e.val r j)
                  = e.val r c * (e.val r c)⁻¹ * e.val r j := by rw [← mul_assoc]
                _ = 1 * e.val r j := by rw [hp1]
                _ = e.val r j := by rw [one_mul]
            have hNeg : e.val r c * -((e.val r c)⁻¹ * e.val r j) =
                -(e.val r c * ((e.val r c)⁻¹ * e.val r j)) := by rw [mul_neg]
            rw [hNeg, hAssoc, add_neg_cancel]

theorem isIsolatedEntry_pivotClearedEquiv (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0)
    (hg : IsGreatest {i | e.val i c ≠ 0} r)
    (hc : IsLeast (Set.univ : Set n) c) :
    IsolatedEntry (pivotClearedEquiv e r c hp) r c where
  row_zero j hj := by
    have h := pivotClearedEquiv_row_isolated_of_isLeast e r c hp hc j
    rw [h, ite_eq_right hj]
  col_zero i hi := by
    have h := pivotClearedEquiv_col_isolated_of_isGreatest e r c hp hg i
    rw [h, ite_eq_right hi]

/-- Factorization recovering `e` from inverse left/right factors. -/
theorem pivotClearedEquiv_factorization (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) :
    e = ((GeneralLinearEquiv.ofGL (rowClear e.val r c hp)).symm.trans
          (pivotClearedEquiv e r c hp)).trans
          (GeneralLinearEquiv.ofGL (columnClear e.val r c hp)).symm := by
  set L := GeneralLinearEquiv.ofGL (rowClear e.val r c hp)
  set R := GeneralLinearEquiv.ofGL (columnClear e.val r c hp)
  have hPivot : pivotClearedEquiv e r c hp = (L.trans e).trans R := rfl
  calc e
      = (GeneralLinearEquiv.refl : GeneralLinearEquiv m m K).trans e := (refl_trans e).symm
    _ = (L.symm.trans L).trans e :=
          congrArg (fun x => x.trans e) (symm_trans L).symm
    _ = L.symm.trans (L.trans e) := trans_assoc _ _ _
    _ = L.symm.trans ((L.trans e).trans
          (GeneralLinearEquiv.refl : GeneralLinearEquiv n n K)) :=
          congrArg (fun x => L.symm.trans x) (trans_refl (L.trans e)).symm
    _ = L.symm.trans ((L.trans e).trans (R.trans R.symm)) :=
          congrArg (fun y => L.symm.trans ((L.trans e).trans y))
            (trans_symm R).symm
    _ = L.symm.trans (((L.trans e).trans R).trans R.symm) :=
          congrArg (fun y => L.symm.trans y) (trans_assoc _ _ _).symm
    _ = (L.symm.trans ((L.trans e).trans R)).trans R.symm :=
          (trans_assoc _ _ _).symm
    _ = (L.symm.trans (pivotClearedEquiv e r c hp)).trans R.symm := by rw [hPivot]

end PivotBoth

/-! ### C. Canonical pivot selection -/

section ColumnSupportDef

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable {K : Type*} [DivisionRing K]

/-- Column support: rows with nonzero entry in column `c`. -/
noncomputable def columnSupport (e : GeneralLinearEquiv m n K) (c : n) : Finset m :=
  haveI : DecidablePred (fun i : m => e.val i c ≠ 0) := Classical.decPred _
  Finset.univ.filter fun i => e.val i c ≠ 0

@[simp]
theorem mem_columnSupport {e : GeneralLinearEquiv m n K} {c : n} {i : m} :
    i ∈ columnSupport e c ↔ e.val i c ≠ 0 := by
  classical
  simp [columnSupport]

theorem columnSupport_nonempty (e : GeneralLinearEquiv m n K) (c : n) :
    (columnSupport e c).Nonempty := by
  classical
  by_contra hEmpty
  rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
  have hAllZero : ∀ i : m, e.val i c = 0 := by
    intro i
    by_contra hNe
    have : i ∈ columnSupport e c := by rwa [mem_columnSupport]
    rw [hEmpty] at this
    exact Finset.notMem_empty i this
  have hMul : e.inv * e.val = 1 := e.inv_val
  have hCC : (e.inv * e.val) c c = (1 : Matrix n n K) c c := by rw [hMul]
  have hOne : (1 : Matrix n n K) c c = (1 : K) := by simp [Matrix.one_apply_eq]
  have hZero : (e.inv * e.val) c c = 0 := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    simp [hAllZero k]
  rw [hZero, hOne] at hCC
  exact one_ne_zero hCC.symm

end ColumnSupportDef

section PivotRowDef

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m]
variable {K : Type*} [DivisionRing K]

/-- Bottommost nonzero row in column `c`. -/
noncomputable def pivotRow (e : GeneralLinearEquiv m n K) (c : n) : m :=
  (columnSupport e c).max' (columnSupport_nonempty e c)

theorem pivotRow_mem_columnSupport (e : GeneralLinearEquiv m n K) (c : n) :
    pivotRow e c ∈ columnSupport e c :=
  Finset.max'_mem _ _

theorem pivotRow_ne_zero (e : GeneralLinearEquiv m n K) (c : n) :
    e.val (pivotRow e c) c ≠ 0 := by
  rw [← mem_columnSupport]
  exact pivotRow_mem_columnSupport e c

theorem pivotRow_le (e : GeneralLinearEquiv m n K) (c : n) (i : m)
    (hi : i ∈ columnSupport e c) :
    i ≤ pivotRow e c :=
  Finset.le_max' _ _ hi

theorem pivotRow_isGreatest (e : GeneralLinearEquiv m n K) (c : n) :
    IsGreatest {i | e.val i c ≠ 0} (pivotRow e c) := by
  constructor
  · exact pivotRow_ne_zero e c
  · intro j hj
    exact pivotRow_le e c j (by rwa [mem_columnSupport])

theorem pivotRow_gt_eq_zero (e : GeneralLinearEquiv m n K) (c : n) (i : m)
    (hi : pivotRow e c < i) : e.val i c = 0 := by
  by_contra hNe
  exact not_le_of_gt hi (pivotRow_le e c i (by rwa [mem_columnSupport]))

end PivotRowDef

section CanonicalColumnDef

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n] [Nonempty n]

/-- Canonical pivot column is `leastIndex` of `n`. -/
noncomputable def canonicalColumn : n :=
  Matrix.GeneralLinearGroup.leastIndex (ι := n)

end CanonicalColumnDef

section CanonicalColumnIsLeast

variable {n : Type*} [Fintype n] [LinearOrder n] [Nonempty n]

theorem canonicalColumn_isLeast :
    IsLeast (Set.univ : Set n) (canonicalColumn : n) := by
  unfold canonicalColumn
  exact Matrix.GeneralLinearGroup.leastIndex_isLeast (ι := n)

end CanonicalColumnIsLeast

section CanonicalPivotDefs

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n] [Nonempty n]
variable {K : Type*} [DivisionRing K]

noncomputable def canonicalPivotRow (e : GeneralLinearEquiv m n K) : m :=
  pivotRow e canonicalColumn

theorem canonicalPivotRow_ne_zero (e : GeneralLinearEquiv m n K) :
    e.val (canonicalPivotRow e) (canonicalColumn : n) ≠ 0 :=
  pivotRow_ne_zero e _

theorem canonicalPivotRow_isGreatest (e : GeneralLinearEquiv m n K) :
    IsGreatest {i | e.val i (canonicalColumn : n) ≠ 0} (canonicalPivotRow e) :=
  pivotRow_isGreatest e _

noncomputable def canonicalPivotCleared (e : GeneralLinearEquiv m n K) :
    GeneralLinearEquiv m n K :=
  pivotClearedEquiv e (canonicalPivotRow e) (canonicalColumn : n)
    (canonicalPivotRow_ne_zero e)

theorem canonicalPivotCleared_col_isolated (e : GeneralLinearEquiv m n K)
    (i : m) :
    (canonicalPivotCleared e).val i (canonicalColumn : n) =
      if i = canonicalPivotRow e then
        e.val (canonicalPivotRow e) (canonicalColumn : n) else 0 :=
  pivotClearedEquiv_col_isolated_of_isGreatest e _ _ _
    (canonicalPivotRow_isGreatest e) i

theorem canonicalPivotCleared_row_isolated (e : GeneralLinearEquiv m n K)
    (j : n) :
    (canonicalPivotCleared e).val (canonicalPivotRow e) j =
      if j = (canonicalColumn : n) then
        e.val (canonicalPivotRow e) (canonicalColumn : n) else 0 :=
  pivotClearedEquiv_row_isolated_of_isLeast e _ _ _
    canonicalColumn_isLeast j

theorem canonicalPivotCleared_isIsolated (e : GeneralLinearEquiv m n K) :
    IsolatedEntry (canonicalPivotCleared e)
      (canonicalPivotRow e) (canonicalColumn : n) :=
  isIsolatedEntry_pivotClearedEquiv e _ _ _
    (canonicalPivotRow_isGreatest e) canonicalColumn_isLeast

/-- Canonical pivot unit `e.val r c`. -/
noncomputable def canonicalPivotUnit (e : GeneralLinearEquiv m n K) : Kˣ :=
  isolatedPivotUnit (canonicalPivotCleared_isIsolated e)

theorem coe_canonicalPivotUnit (e : GeneralLinearEquiv m n K) :
    (canonicalPivotUnit e : K) = e.val (canonicalPivotRow e) (canonicalColumn : n) := by
  have h : (canonicalPivotCleared e).val (canonicalPivotRow e) (canonicalColumn : n) =
      e.val (canonicalPivotRow e) (canonicalColumn : n) :=
    pivotClearedEquiv_pivot e _ _ _
  calc (canonicalPivotUnit e : K)
      = (canonicalPivotCleared e).val (canonicalPivotRow e) (canonicalColumn : n) := rfl
    _ = e.val (canonicalPivotRow e) (canonicalColumn : n) := h

/-- Reduced equivalence after deleting isolated pivot row and column. -/
noncomputable def reducedPivotEquiv (e : GeneralLinearEquiv m n K) :
    GeneralLinearEquiv (DeletedIndex m (canonicalPivotRow e))
      (DeletedIndex n (canonicalColumn : n)) K :=
  deleteEntryEquiv (canonicalPivotCleared_isIsolated e)

theorem card_DeletedIndex_row (e : GeneralLinearEquiv m n K) :
    Fintype.card (DeletedIndex m (canonicalPivotRow e)) =
      Fintype.card m - 1 :=
  Matrix.GeneralLinearGroup.card_DeletedIndex (canonicalPivotRow e)

theorem card_DeletedIndex_col :
    Fintype.card (DeletedIndex n (canonicalColumn : n)) =
      Fintype.card n - 1 :=
  Matrix.GeneralLinearGroup.card_DeletedIndex (canonicalColumn : n)

theorem canonical_reconstruction (e : GeneralLinearEquiv m n K) :
    insertEntryEquiv (canonicalPivotRow e) (canonicalColumn : n)
        (canonicalPivotUnit e) (reducedPivotEquiv e) =
      canonicalPivotCleared e :=
  insert_delete_reconstruction (canonicalPivotCleared_isIsolated e)

theorem canonical_factorization (e : GeneralLinearEquiv m n K) :
    e = ((GeneralLinearEquiv.ofGL
            (rowClear e.val (canonicalPivotRow e) (canonicalColumn : n)
              (canonicalPivotRow_ne_zero e))).symm.trans
          (canonicalPivotCleared e)).trans
          (GeneralLinearEquiv.ofGL
            (columnClear e.val (canonicalPivotRow e) (canonicalColumn : n)
              (canonicalPivotRow_ne_zero e))).symm :=
  pivotClearedEquiv_factorization e _ _ _

end CanonicalPivotDefs

/-! ### D. Coefficient functoriality -/

section DivRingLemmas

variable {K L : Type*} [DivisionRing K] [DivisionRing L]

theorem divRingHom_map_ne_zero (f : K →+* L) {a : K} (ha : a ≠ 0) : f a ≠ 0 := by
  intro h0
  have h1 : f (a * a⁻¹) = f 1 := by rw [mul_inv_cancel₀ ha]
  have hMul : f a * f a⁻¹ = 1 := by
    calc f a * f a⁻¹ = f (a * a⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [h1]
      _ = 1 := f.map_one
  rw [h0, zero_mul] at hMul
  exact one_ne_zero hMul.symm

theorem divRingHom_injective_of_div (f : K →+* L) : Function.Injective f := by
  intro a b hab
  by_contra hne
  have hSub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hMap : f (a - b) = 0 := by rw [f.map_sub, hab, sub_self]
  exact divRingHom_map_ne_zero f hSub hMap

theorem divRingHom_map_inv (f : K →+* L) {a : K} (ha : a ≠ 0) :
    f a⁻¹ = (f a)⁻¹ := by
  have hfaNe : f a ≠ 0 := divRingHom_map_ne_zero f ha
  have h1 : f a * f a⁻¹ = 1 := by
    have : f (a * a⁻¹) = f 1 := by rw [mul_inv_cancel₀ ha]
    calc f a * f a⁻¹ = f (a * a⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [this]
      _ = 1 := f.map_one
  have h2 : (f a)⁻¹ * f a = 1 := inv_mul_cancel₀ hfaNe
  calc f a⁻¹ = 1 * f a⁻¹ := by rw [one_mul]
    _ = ((f a)⁻¹ * f a) * f a⁻¹ := by rw [h2]
    _ = (f a)⁻¹ * (f a * f a⁻¹) := by rw [mul_assoc]
    _ = (f a)⁻¹ * 1 := by rw [h1]
    _ = (f a)⁻¹ := by rw [mul_one]

end DivRingLemmas

section ColumnSupportMap

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

theorem columnSupport_map (e : GeneralLinearEquiv m n K) (c : n) (f : K →+* L) :
    columnSupport (e.map f) c = columnSupport e c := by
  classical
  ext i
  simp only [mem_columnSupport, val_map, Matrix.map_apply]
  constructor
  · intro h h0
    have : f (e.val i c) = 0 := by rw [h0, f.map_zero]
    exact h this
  · intro h h0
    exact h ((divRingHom_injective_of_div f) (by rw [h0, f.map_zero]))

end ColumnSupportMap

section PivotRowMap

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

theorem pivotRow_map (e : GeneralLinearEquiv m n K) (c : n) (f : K →+* L) :
    pivotRow (e.map f) c = pivotRow e c := by
  classical
  have hSetEq : {i : m | (e.map f).val i c ≠ 0} = {i | e.val i c ≠ 0} := by
    ext i
    simp only [val_map, Matrix.map_apply, ne_eq]
    constructor
    · intro h h0
      have : f (e.val i c) = 0 := by rw [h0, f.map_zero]
      exact h this
    · intro h h0
      exact h ((divRingHom_injective_of_div f) (by rw [h0, f.map_zero]))
  have hg1 : IsGreatest {i | e.val i c ≠ 0} (pivotRow e c) := pivotRow_isGreatest e c
  have hg2 : IsGreatest {i | (e.map f).val i c ≠ 0} (pivotRow (e.map f) c) :=
    pivotRow_isGreatest (e.map f) c
  have hg2' : IsGreatest {i | e.val i c ≠ 0} (pivotRow (e.map f) c) := by rwa [← hSetEq]
  exact le_antisymm (hg1.2 hg2'.1) (hg2'.2 hg1.1)

end PivotRowMap

section RowClearCoeffsMap

variable {m n : Type*} [LinearOrder m]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

theorem rowClearCoeffs_map (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (f : K →+* L) (hp' : (M.map ⇑f) r c ≠ 0)
    (i : RowIdx m r) :
    Matrix.GeneralLinearGroup.multiplicativeMap f (rowClearCoeffs M r c hp i) =
      rowClearCoeffs (M.map ⇑f) r c hp' i := by
  apply congrArg Multiplicative.ofAdd
  calc f (-(M i.val c * (M r c)⁻¹))
      = -(f (M i.val c * (M r c)⁻¹)) := by rw [f.map_neg]
    _ = -(f (M i.val c) * f ((M r c)⁻¹)) := by rw [f.map_mul]
    _ = -(f (M i.val c) * (f (M r c))⁻¹) := by rw [divRingHom_map_inv f hp]
    _ = -((M.map ⇑f) i.val c * ((M.map ⇑f) r c)⁻¹) := rfl

end RowClearCoeffsMap

section ColClearCoeffsMap

variable {m n : Type*} [LinearOrder n]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

theorem columnClearCoeffs_map (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (f : K →+* L) (hp' : (M.map ⇑f) r c ≠ 0)
    (j : ColIdx n c) :
    Matrix.GeneralLinearGroup.multiplicativeMap f (columnClearCoeffs M r c hp j) =
      columnClearCoeffs (M.map ⇑f) r c hp' j := by
  apply congrArg Multiplicative.ofAdd
  calc f (-((M r c)⁻¹ * M r j.val))
      = -(f ((M r c)⁻¹ * M r j.val)) := by rw [f.map_neg]
    _ = -(f ((M r c)⁻¹) * f (M r j.val)) := by rw [f.map_mul]
    _ = -((f (M r c))⁻¹ * f (M r j.val)) := by rw [divRingHom_map_inv f hp]
    _ = -(((M.map ⇑f) r c)⁻¹ * (M.map ⇑f) r j.val) := rfl

end ColClearCoeffsMap

section RowClearMap

variable {m : Type*} [DecidableEq m] [Fintype m] [LinearOrder m]
variable {n : Type*}
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

theorem rowClear_map (M : Matrix m n K) (r : m) (c : n) (hp : M r c ≠ 0)
    (f : K →+* L) (hp' : (M.map ⇑f) r c ≠ 0) :
    Matrix.GeneralLinearGroup.mapRingHom (n := m) f (rowClear M r c hp) =
      rowClear (M.map ⇑f) r c hp' := by
  unfold rowClear
  rw [Matrix.GeneralLinearGroup.rowSweep_mapRingHom]
  congr 1
  funext i
  exact rowClearCoeffs_map M r c hp f hp' i

theorem upperRowClear_map (M : Matrix m n K) (r : m) (c : n) (hp : M r c ≠ 0)
    (f : K →+* L) (hp' : (M.map ⇑f) r c ≠ 0) :
    UpperElementary.mapRingHom (ι := m) f (upperRowClear M r c hp) =
      upperRowClear (M.map ⇑f) r c hp' := by
  apply Subtype.ext
  simp only [UpperElementary.coe_mapRingHom]
  exact rowClear_map M r c hp f hp'

end RowClearMap

section ColClearMap

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]
variable {m : Type*}
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

theorem columnClear_map (M : Matrix m n K) (r : m) (c : n) (hp : M r c ≠ 0)
    (f : K →+* L) (hp' : (M.map ⇑f) r c ≠ 0) :
    Matrix.GeneralLinearGroup.mapRingHom (n := n) f (columnClear M r c hp) =
      columnClear (M.map ⇑f) r c hp' := by
  unfold columnClear
  rw [Matrix.GeneralLinearGroup.columnSweep_mapRingHom]
  congr 1
  funext j
  exact columnClearCoeffs_map M r c hp f hp' j

theorem upperColumnClear_map (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (f : K →+* L) (hp' : (M.map ⇑f) r c ≠ 0) :
    UpperElementary.mapRingHom (ι := n) f (upperColumnClear M r c hp) =
      upperColumnClear (M.map ⇑f) r c hp' := by
  apply Subtype.ext
  simp only [UpperElementary.coe_mapRingHom]
  exact columnClear_map M r c hp f hp'

end ColClearMap

section MatrixMapMulLemmas

variable {m n : Type*} [Fintype m] [Fintype n]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]
variable (f : K →+* L)

omit [Fintype n] in
private theorem matrixMapMul (A : Matrix m m K) (B : Matrix m n K) :
    (A * B).map ⇑f = A.map ⇑f * B.map ⇑f := by
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, map_sum, f.map_mul]

omit [Fintype m] in
private theorem matrixMapMulRect (A : Matrix m n K) (B : Matrix n n K) :
    (A * B).map ⇑f = A.map ⇑f * B.map ⇑f := by
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, map_sum, f.map_mul]

private theorem matrixMapMulThree (A : Matrix m m K) (B : Matrix m n K)
    (C : Matrix n n K) :
    (A * B * C).map ⇑f = A.map ⇑f * B.map ⇑f * C.map ⇑f := by
  calc (A * B * C).map ⇑f
      = ((A * B) * C).map ⇑f := rfl
    _ = (A * B).map ⇑f * C.map ⇑f := matrixMapMulRect (f := f) (A * B) C
    _ = (A.map ⇑f * B.map ⇑f) * C.map ⇑f := by rw [matrixMapMul (f := f) A B]
    _ = A.map ⇑f * B.map ⇑f * C.map ⇑f := by rw [Matrix.mul_assoc]

end MatrixMapMulLemmas

section PivotMap

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

theorem pivotClearedMatrix_map (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (f : K →+* L) :
    (pivotClearedMatrix M r c hp).map ⇑f =
      pivotClearedMatrix (M.map ⇑f) r c (divRingHom_map_ne_zero f hp) := by
  unfold pivotClearedMatrix
  have hfNe : (M.map ⇑f) r c ≠ 0 := divRingHom_map_ne_zero f hp
  have hL : ((rowClear M r c hp : GL m K) : Matrix m m K).map ⇑f =
      ((rowClear (M.map ⇑f) r c hfNe : GL m L) : Matrix m m L) := by
    calc ((rowClear M r c hp : GL m K) : Matrix m m K).map ⇑f
        = ((Matrix.GeneralLinearGroup.mapRingHom (n := m) f (rowClear M r c hp) :
          GL m L) : Matrix m m L) := by
          rw [Matrix.GeneralLinearGroup.coe_mapRingHom]
      _ = ((rowClear (M.map ⇑f) r c hfNe : GL m L) : Matrix m m L) := by
          rw [rowClear_map M r c hp f hfNe]
  have hR : ((columnClear M r c hp : GL n K) : Matrix n n K).map ⇑f =
      ((columnClear (M.map ⇑f) r c hfNe : GL n L) : Matrix n n L) := by
    calc ((columnClear M r c hp : GL n K) : Matrix n n K).map ⇑f
        = ((Matrix.GeneralLinearGroup.mapRingHom (n := n) f (columnClear M r c hp) :
          GL n L) : Matrix n n L) := by
          rw [Matrix.GeneralLinearGroup.coe_mapRingHom]
      _ = ((columnClear (M.map ⇑f) r c hfNe : GL n L) : Matrix n n L) := by
          rw [columnClear_map M r c hp f hfNe]
  -- Use the three-factor map lemma proved in the previous section
  have hThree :
      (((rowClear M r c hp : GL m K) : Matrix m m K) * M *
        ((columnClear M r c hp : GL n K) : Matrix n n K)).map ⇑f =
      ((rowClear M r c hp : GL m K) : Matrix m m K).map ⇑f * M.map ⇑f *
        ((columnClear M r c hp : GL n K) : Matrix n n K).map ⇑f := by
    calc (((rowClear M r c hp : GL m K) : Matrix m m K) * M *
          ((columnClear M r c hp : GL n K) : Matrix n n K)).map ⇑f
        = (((rowClear M r c hp : GL m K) : Matrix m m K) * M *
            ((columnClear M r c hp : GL n K) : Matrix n n K)).map ⇑f := rfl
      _ = (((rowClear M r c hp : GL m K) : Matrix m m K) * M).map ⇑f *
            ((columnClear M r c hp : GL n K) : Matrix n n K).map ⇑f := by
          rw [matrixMapMulRect (f := f)]
      _ = (((rowClear M r c hp : GL m K) : Matrix m m K).map ⇑f * M.map ⇑f) *
            ((columnClear M r c hp : GL n K) : Matrix n n K).map ⇑f := by
          rw [matrixMapMul (f := f)]
      _ = ((rowClear M r c hp : GL m K) : Matrix m m K).map ⇑f * M.map ⇑f *
            ((columnClear M r c hp : GL n K) : Matrix n n K).map ⇑f := by
          rw [Matrix.mul_assoc]
  rw [hThree]
  rw [hL, hR]

theorem pivotClearedEquiv_map (e : GeneralLinearEquiv m n K) (r : m) (c : n)
    (hp : e.val r c ≠ 0) (f : K →+* L) :
    (pivotClearedEquiv e r c hp).map f =
      pivotClearedEquiv (e.map f) r c (divRingHom_map_ne_zero f hp) := by
  apply GeneralLinearEquiv.ext
  simp only [val_map, val_pivotClearedEquiv]
  exact pivotClearedMatrix_map (f := f) e.val r c hp

end PivotMap

section CanonicalNat

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n] [Nonempty n]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]
variable (e : GeneralLinearEquiv m n K) (f : K →+* L)

theorem canonicalPivotRow_map :
    pivotRow (e.map f) (canonicalColumn : n) = pivotRow e (canonicalColumn : n) :=
  pivotRow_map e _ f

theorem canonicalPivotCleared_map :
    (canonicalPivotCleared e).map f = canonicalPivotCleared (e.map f) := by
  apply GeneralLinearEquiv.ext
  have hRowEq :
      pivotRow (e.map f) (canonicalColumn : n) = pivotRow e (canonicalColumn : n) :=
    pivotRow_map e _ f
  have hp : e.val (pivotRow e (canonicalColumn : n)) (canonicalColumn : n) ≠ 0 :=
    pivotRow_ne_zero e _
  have hfNe :
      (e.val.map ⇑f) (pivotRow e (canonicalColumn : n)) (canonicalColumn : n) ≠ 0 :=
    divRingHom_map_ne_zero f hp
  have hMap := pivotClearedMatrix_map (f := f) e.val
    (pivotRow e (canonicalColumn : n)) (canonicalColumn : n) hp
  have hLeftVal : ((canonicalPivotCleared e).map f).val =
      pivotClearedMatrix (e.val.map ⇑f) (pivotRow e (canonicalColumn : n))
        (canonicalColumn : n) hfNe := by
    calc ((canonicalPivotCleared e).map f).val
        = ((canonicalPivotCleared e).val.map ⇑f) := rfl
      _ = (pivotClearedMatrix e.val (pivotRow e (canonicalColumn : n))
            (canonicalColumn : n) hp).map ⇑f := rfl
      _ = pivotClearedMatrix (e.val.map ⇑f) (pivotRow e (canonicalColumn : n))
            (canonicalColumn : n) hfNe := hMap
  have hRightVal : (canonicalPivotCleared (e.map f)).val =
      pivotClearedMatrix (e.val.map ⇑f) (pivotRow (e.map f) (canonicalColumn : n))
        (canonicalColumn : n) (pivotRow_ne_zero (e.map f) (canonicalColumn : n)) := rfl
  rw [hLeftVal, hRightVal]
  exact pivotClearedMatrix_eq_of_row_eq
    (e.val.map ⇑f)
    (pivotRow e (canonicalColumn : n))
    (pivotRow (e.map f) (canonicalColumn : n))
    (canonicalColumn : n)
    hfNe
    (pivotRow_ne_zero (e.map f) (canonicalColumn : n))
    hRowEq

theorem canonicalPivotUnit_map :
    Units.map f (canonicalPivotUnit e) = canonicalPivotUnit (e.map f) := by
  have hRowEq :
      pivotRow (e.map f) (canonicalColumn : n) = pivotRow e (canonicalColumn : n) :=
    pivotRow_map e _ f
  apply Units.ext
  have h1 : (canonicalPivotUnit e : K) =
      e.val (canonicalPivotRow e) (canonicalColumn : n) :=
    coe_canonicalPivotUnit e
  have h2 : (canonicalPivotUnit (e.map f) : L) =
      (e.map f).val (canonicalPivotRow (e.map f)) (canonicalColumn : n) :=
    coe_canonicalPivotUnit (e.map f)
  have h3 : (e.map f).val (canonicalPivotRow (e.map f)) (canonicalColumn : n) =
      f (e.val (canonicalPivotRow (e.map f)) (canonicalColumn : n)) := rfl
  have h4 : e.val (canonicalPivotRow (e.map f)) (canonicalColumn : n) =
      e.val (canonicalPivotRow e) (canonicalColumn : n) :=
    congrArg (fun r => e.val r (canonicalColumn : n)) hRowEq
  calc (Units.map f (canonicalPivotUnit e)).val
      = f (canonicalPivotUnit e).val := rfl
    _ = f (e.val (canonicalPivotRow e) (canonicalColumn : n)) := by rw [h1]
    _ = f (e.val (canonicalPivotRow (e.map f)) (canonicalColumn : n)) := by rw [← h4]
    _ = (e.map f).val (canonicalPivotRow (e.map f)) (canonicalColumn : n) := by rw [← h3]
    _ = (canonicalPivotUnit (e.map f)).val := by rw [← h2]

/-- Naturality for reduced deletion, entrywise. -/
theorem reducedPivotEquiv_map
    (i : DeletedIndex m (canonicalPivotRow e))
    (j : DeletedIndex n (canonicalColumn : n)) :
    ((reducedPivotEquiv e).map f).val i j =
      (reducedPivotEquiv (e.map f)).val
        ⟨i.val, by
          intro hEq
          have hRowEq :
              pivotRow (e.map f) (canonicalColumn : n) =
                pivotRow e (canonicalColumn : n) :=
            pivotRow_map e (canonicalColumn : n) f
          have : i.val = canonicalPivotRow e := hEq.trans hRowEq
          exact i.prop this⟩ j := by
  have hRowEq :
      pivotRow (e.map f) (canonicalColumn : n) =
        pivotRow e (canonicalColumn : n) :=
    pivotRow_map e (canonicalColumn : n) f
  have hClearedMap := canonicalPivotCleared_map e f
  have hValEq : ((canonicalPivotCleared e).map f).val =
      (canonicalPivotCleared (e.map f)).val := by rw [hClearedMap]
  calc ((reducedPivotEquiv e).map f).val i j
      = f ((reducedPivotEquiv e).val i j) := rfl
    _ = f ((canonicalPivotCleared e).val i.val j.val) := rfl
    _ = ((canonicalPivotCleared e).val.map ⇑f) i.val j.val := rfl
    _ = ((canonicalPivotCleared e).map f).val i.val j.val := rfl
    _ = (canonicalPivotCleared (e.map f)).val i.val j.val := by rw [hValEq]
    _ = (reducedPivotEquiv (e.map f)).val
          ⟨i.val, by
            intro hEq
            have : i.val = canonicalPivotRow e := hEq.trans hRowEq
            exact i.prop this⟩ j := rfl

end CanonicalNat

section DeletedIndexEquiv

variable {α : Type*}

/-- `DeletedIndex` equivalence from equality of the deleted point. -/
def deletedIndexEquivOfEq {r₁ r₂ : α} (h : r₁ = r₂) :
    DeletedIndex α r₁ ≃ DeletedIndex α r₂ where
  toFun x := ⟨x.val, fun heq => x.prop (heq.trans h.symm)⟩
  invFun y := ⟨y.val, fun heq => y.prop (heq.trans h)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

end DeletedIndexEquiv

section ReducedPivotEquivMapEq

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n] [Nonempty n]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]
variable (e : GeneralLinearEquiv m n K) (f : K →+* L)

/-- Equality-level naturality for `reducedPivotEquiv` across a division-ring hom. -/
theorem reducedPivotEquiv_map_eq_reindex :
    (reducedPivotEquiv e).map f =
      (reducedPivotEquiv (e.map f)).reindex
        (deletedIndexEquivOfEq (canonicalPivotRow_map e f).symm)
        (Equiv.refl (DeletedIndex n (canonicalColumn : n))) := by
  apply GeneralLinearEquiv.ext
  ext i j
  rw [reducedPivotEquiv_map e f i j]
  rfl

end ReducedPivotEquivMapEq

section SweepOne

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [Ring R]

/-- `rowSweep r 1 = 1` (GL version). -/
theorem rowSweep_one (r : ι) :
    Matrix.GeneralLinearGroup.rowSweep (R := R) r
      (1 : Matrix.GeneralLinearGroup.RowIdx ι r → Multiplicative R) = 1 :=
  (Matrix.GeneralLinearGroup.rowSweep (R := R) r).map_one

/-- `columnSweep c 1 = 1` (GL version). -/
theorem columnSweep_one (c : ι) :
    Matrix.GeneralLinearGroup.columnSweep (R := R) c
      (1 : Matrix.GeneralLinearGroup.ColIdx ι c → Multiplicative R) = 1 :=
  (Matrix.GeneralLinearGroup.columnSweep (R := R) c).map_one

/-- `U` version of `rowSweep r 1 = 1`. -/
theorem upperRowSweep_one (r : ι) :
    Matrix.GeneralLinearGroup.UpperElementary.rowSweep (R := R) r
      (1 : Matrix.GeneralLinearGroup.RowIdx ι r → Multiplicative R) = 1 := by
  apply Subtype.ext
  simp

/-- `U` version of `columnSweep c 1 = 1`. -/
theorem upperColumnSweep_one (c : ι) :
    Matrix.GeneralLinearGroup.UpperElementary.columnSweep (R := R) c
      (1 : Matrix.GeneralLinearGroup.ColIdx ι c → Multiplicative R) = 1 := by
  apply Subtype.ext
  simp

end SweepOne

section RowClearTrivial

variable {m : Type*} [DecidableEq m] [Fintype m] [LinearOrder m]
variable {n : Type*}
variable {K : Type*} [DivisionRing K]

omit [DecidableEq m] [Fintype m] in
/-- Coefficients become `1` when column `c` is zero above `r`. -/
theorem rowClearCoeffs_eq_one_of_forall_lt_eq_zero (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ i : m, i < r → M i c = 0) :
    rowClearCoeffs M r c hp = 1 := by
  funext i
  have hi : M i.val c = 0 := h i.val i.prop
  simp only [Pi.one_apply, rowClearCoeffs, hi, zero_mul, neg_zero]
  rfl

/-- `rowClear` is `1` when column `c` is zero above `r`. -/
theorem rowClear_eq_one_of_forall_lt_eq_zero (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ i : m, i < r → M i c = 0) :
    rowClear M r c hp = 1 := by
  unfold rowClear
  rw [rowClearCoeffs_eq_one_of_forall_lt_eq_zero M r c hp h, rowSweep_one]

/-- `U` version. -/
theorem upperRowClear_eq_one_of_forall_lt_eq_zero (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ i : m, i < r → M i c = 0) :
    upperRowClear M r c hp = 1 := by
  apply Subtype.ext
  simp only [coe_upperRowClear, rowClear_eq_one_of_forall_lt_eq_zero M r c hp h, Subgroup.coe_one]

/-- Singleton column support implies `rowClear = 1`. -/
theorem rowClear_eq_one_of_forall_ne_zero_eq (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ i : m, M i c ≠ 0 → i = r) :
    rowClear M r c hp = 1 := by
  apply rowClear_eq_one_of_forall_lt_eq_zero M r c hp
  intro i hi
  by_contra hNe
  have hEq : i = r := h i hNe
  have : r < r := hEq ▸ hi
  exact lt_irrefl _ this

theorem upperRowClear_eq_one_of_forall_ne_zero_eq (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ i : m, M i c ≠ 0 → i = r) :
    upperRowClear M r c hp = 1 := by
  apply upperRowClear_eq_one_of_forall_lt_eq_zero M r c hp
  intro i hi
  by_contra hNe
  have hEq : i = r := h i hNe
  have : r < r := hEq ▸ hi
  exact lt_irrefl _ this

end RowClearTrivial

section ColClearTrivial

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]
variable {m : Type*}
variable {K : Type*} [DivisionRing K]

omit [DecidableEq n] [Fintype n] in
/-- Coefficients become `1` when row `r` is zero to the right of `c`. -/
theorem columnClearCoeffs_eq_one_of_forall_gt_eq_zero (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ j : n, c < j → M r j = 0) :
    columnClearCoeffs M r c hp = 1 := by
  funext j
  have hj : M r j.val = 0 := h j.val j.prop
  simp only [Pi.one_apply, columnClearCoeffs, hj, mul_zero, neg_zero]
  rfl

theorem columnClear_eq_one_of_forall_gt_eq_zero (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ j : n, c < j → M r j = 0) :
    columnClear M r c hp = 1 := by
  unfold columnClear
  rw [columnClearCoeffs_eq_one_of_forall_gt_eq_zero M r c hp h, columnSweep_one]

theorem upperColumnClear_eq_one_of_forall_gt_eq_zero (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ j : n, c < j → M r j = 0) :
    upperColumnClear M r c hp = 1 := by
  apply Subtype.ext
  simp only [coe_upperColumnClear,
    columnClear_eq_one_of_forall_gt_eq_zero M r c hp h, Subgroup.coe_one]

theorem columnClear_eq_one_of_forall_ne_zero_eq (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ j : n, M r j ≠ 0 → j = c) :
    columnClear M r c hp = 1 := by
  apply columnClear_eq_one_of_forall_gt_eq_zero M r c hp
  intro j hj
  by_contra hNe
  have hEq : j = c := h j hNe
  have : c < c := hEq ▸ hj
  exact lt_irrefl _ this

theorem upperColumnClear_eq_one_of_forall_ne_zero_eq (M : Matrix m n K) (r : m) (c : n)
    (hp : M r c ≠ 0) (h : ∀ j : n, M r j ≠ 0 → j = c) :
    upperColumnClear M r c hp = 1 := by
  apply upperColumnClear_eq_one_of_forall_gt_eq_zero M r c hp
  intro j hj
  by_contra hNe
  have hEq : j = c := h j hNe
  have : c < c := hEq ▸ hj
  exact lt_irrefl _ this

end ColClearTrivial

section RowSupportDef

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable {K : Type*} [DivisionRing K]

/-- Row support: columns with nonzero entry in row `r`. -/
noncomputable def rowSupport (e : GeneralLinearEquiv m n K) (r : m) : Finset n :=
  haveI : DecidablePred (fun j : n => e.val r j ≠ 0) := Classical.decPred _
  Finset.univ.filter fun j => e.val r j ≠ 0

@[simp]
theorem mem_rowSupport {e : GeneralLinearEquiv m n K} {r : m} {j : n} :
    j ∈ rowSupport e r ↔ e.val r j ≠ 0 := by
  classical
  simp [rowSupport]

end RowSupportDef

section MonomialSupportLemmas

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

omit [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n] in
@[simp]
theorem monomialEquiv_units_val_ne_zero (w : m → Kˣ) (i : m) : (w i : K) ≠ 0 :=
  (w i).ne_zero

omit [LinearOrder m] [LinearOrder n] in
theorem monomialEquiv_val_ne_zero_iff (w : m → Kˣ) (σ : n ≃ m) (i : m) (j : n) :
    (monomialEquiv (R := K) w σ).val i j ≠ 0 ↔ σ j = i := by
  constructor
  · intro hNe
    by_contra hNot
    have hZero : (monomialEquiv (R := K) w σ).val i j = 0 := by
      rw [val_monomialEquiv_apply, ite_eq_right hNot]
    exact hNe hZero
  · intro hEq
    rw [val_monomialEquiv_apply, ite_eq_left hEq]
    exact (w i).ne_zero

omit [LinearOrder m] [LinearOrder n] in
theorem monomialEquiv_val_eq_zero_iff (w : m → Kˣ) (σ : n ≃ m) (i : m) (j : n) :
    (monomialEquiv (R := K) w σ).val i j = 0 ↔ σ j ≠ i := by
  constructor
  · intro hZero hEq
    have hNe : (monomialEquiv (R := K) w σ).val i j ≠ 0 := by
      rwa [monomialEquiv_val_ne_zero_iff]
    exact hNe hZero
  · intro hNe
    by_cases hEq : σ j = i
    · exact False.elim (hNe hEq)
    · rw [val_monomialEquiv_apply, ite_eq_right hEq]

omit [LinearOrder m] [LinearOrder n] in
theorem monomialEquiv_val_ne_zero_of_eq (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    (monomialEquiv (R := K) w σ).val (σ c) c ≠ 0 := by
  rw [monomialEquiv_val_ne_zero_iff]

omit [LinearOrder m] [LinearOrder n] in
theorem monomialEquiv_val_zero_of_col_ne (w : m → Kˣ) (σ : n ≃ m) {i : m} {c : n}
    (h : i ≠ σ c) : (monomialEquiv (R := K) w σ).val i c = 0 := by
  rw [monomialEquiv_val_eq_zero_iff]
  intro hEq
  exact h hEq.symm

omit [LinearOrder m] [LinearOrder n] in
theorem monomialEquiv_val_zero_of_row_ne (w : m → Kˣ) (σ : n ≃ m) {r : m} {j : n}
    (h : σ j ≠ r) : (monomialEquiv (R := K) w σ).val r j = 0 := by
  rw [monomialEquiv_val_eq_zero_iff]
  exact h

omit [LinearOrder m] [LinearOrder n] in
theorem columnSupport_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    columnSupport (monomialEquiv (R := K) w σ) c = {σ c} := by
  classical
  ext i
  simp only [mem_columnSupport, Finset.mem_singleton]
  rw [monomialEquiv_val_ne_zero_iff]
  exact eq_comm

omit [LinearOrder m] [LinearOrder n] in
theorem rowSupport_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) (r : m) :
    rowSupport (monomialEquiv (R := K) w σ) r = {σ.symm r} := by
  classical
  ext j
  simp only [mem_rowSupport, Finset.mem_singleton]
  constructor
  · intro hNe
    have hEq : σ j = r := (monomialEquiv_val_ne_zero_iff w σ r j).mp hNe
    calc j = σ.symm (σ j) := (σ.symm_apply_apply j).symm
      _ = σ.symm r := by rw [hEq]
  · intro hEq
    have hσ : σ j = r := by
      calc σ j = σ (σ.symm r) := by rw [hEq]
        _ = r := σ.apply_symm_apply r
    rwa [monomialEquiv_val_ne_zero_iff]

omit [LinearOrder m] [LinearOrder n] in
theorem rowSupport_monomialEquiv_iff (w : m → Kˣ) (σ : n ≃ m) (r : m) (j : n) :
    (monomialEquiv (R := K) w σ).val r j ≠ 0 ↔ j = σ.symm r := by
  constructor
  · intro hNe
    have hEq : σ j = r := (monomialEquiv_val_ne_zero_iff w σ r j).mp hNe
    calc j = σ.symm (σ j) := (σ.symm_apply_apply j).symm
      _ = σ.symm r := by rw [hEq]
  · intro hEq
    have hσ : σ j = r := by
      calc σ j = σ (σ.symm r) := by rw [hEq]
        _ = r := σ.apply_symm_apply r
    rwa [monomialEquiv_val_ne_zero_iff]

end MonomialSupportLemmas

section MonomialPivotRow

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

omit [LinearOrder n] in
theorem isGreatest_monomialEquiv_col (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    IsGreatest {i | (monomialEquiv (R := K) w σ).val i c ≠ 0} (σ c) := by
  constructor
  · change (monomialEquiv w σ).val (σ c) c ≠ 0
    rw [monomialEquiv_val_ne_zero_iff]
  · intro i hi
    have hEq : σ c = i := (monomialEquiv_val_ne_zero_iff w σ i c).mp hi
    exact le_of_eq hEq.symm

omit [LinearOrder n] in
theorem pivotRow_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    pivotRow (monomialEquiv (R := K) w σ) c = σ c := by
  have hS : IsGreatest {i | (monomialEquiv (R := K) w σ).val i c ≠ 0} (σ c) :=
    isGreatest_monomialEquiv_col w σ c
  have hg : IsGreatest {i | (monomialEquiv (R := K) w σ).val i c ≠ 0}
      (pivotRow (monomialEquiv (R := K) w σ) c) :=
    pivotRow_isGreatest _ c
  exact le_antisymm (hS.2 hg.1) (hg.2 hS.1)

section Canonical

variable [Nonempty n]

theorem canonicalPivotRow_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) :
    canonicalPivotRow (monomialEquiv (R := K) w σ) = σ (canonicalColumn : n) := by
  unfold canonicalPivotRow
  exact pivotRow_monomialEquiv w σ _

theorem coe_canonicalPivotUnit_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) :
    (canonicalPivotUnit (monomialEquiv (R := K) w σ) : K) = (w (σ (canonicalColumn : n)) : K) := by
  have hRow : canonicalPivotRow (monomialEquiv (R := K) w σ) = σ (canonicalColumn : n) :=
    canonicalPivotRow_monomialEquiv w σ
  calc (canonicalPivotUnit (monomialEquiv (R := K) w σ) : K)
      = (monomialEquiv (R := K) w σ).val
          (canonicalPivotRow (monomialEquiv (R := K) w σ)) (canonicalColumn : n) := by
        rw [coe_canonicalPivotUnit]
    _ = (monomialEquiv (R := K) w σ).val (σ (canonicalColumn : n)) (canonicalColumn : n) := by
        rw [hRow]
    _ = (w (σ (canonicalColumn : n)) : K) := by
        rw [val_monomialEquiv_apply, ite_eq_left rfl]

theorem canonicalPivotUnit_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) :
    canonicalPivotUnit (monomialEquiv (R := K) w σ) = w (σ (canonicalColumn : n)) := by
  apply Units.ext
  exact coe_canonicalPivotUnit_monomialEquiv w σ

end Canonical

end MonomialPivotRow

section MonomialClear

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

omit [LinearOrder n] in
theorem rowClear_monomialEquiv_eq_one (w : m → Kˣ) (σ : n ≃ m) (c : n)
    (hp : (monomialEquiv (R := K) w σ).val (σ c) c ≠ 0) :
    rowClear (monomialEquiv (R := K) w σ).val (σ c) c hp = 1 := by
  apply rowClear_eq_one_of_forall_ne_zero_eq
  intro i hi
  exact ((monomialEquiv_val_ne_zero_iff w σ i c).mp hi).symm

omit [LinearOrder n] in
theorem upperRowClear_monomialEquiv_eq_one (w : m → Kˣ) (σ : n ≃ m) (c : n)
    (hp : (monomialEquiv (R := K) w σ).val (σ c) c ≠ 0) :
    upperRowClear (monomialEquiv (R := K) w σ).val (σ c) c hp = 1 := by
  apply upperRowClear_eq_one_of_forall_ne_zero_eq
  intro i hi
  exact ((monomialEquiv_val_ne_zero_iff w σ i c).mp hi).symm

omit [LinearOrder m] in
theorem columnClear_monomialEquiv_eq_one (w : m → Kˣ) (σ : n ≃ m) (c : n)
    (hp : (monomialEquiv (R := K) w σ).val (σ c) c ≠ 0) :
    columnClear (monomialEquiv (R := K) w σ).val (σ c) c hp = 1 := by
  apply columnClear_eq_one_of_forall_ne_zero_eq
  intro j hj
  have hEq : σ j = σ c := (monomialEquiv_val_ne_zero_iff w σ (σ c) j).mp hj
  exact σ.injective hEq

omit [LinearOrder m] in
theorem upperColumnClear_monomialEquiv_eq_one (w : m → Kˣ) (σ : n ≃ m) (c : n)
    (hp : (monomialEquiv (R := K) w σ).val (σ c) c ≠ 0) :
    upperColumnClear (monomialEquiv (R := K) w σ).val (σ c) c hp = 1 := by
  apply upperColumnClear_eq_one_of_forall_ne_zero_eq
  intro j hj
  have hEq : σ j = σ c := (monomialEquiv_val_ne_zero_iff w σ (σ c) j).mp hj
  exact σ.injective hEq

omit [LinearOrder n] in
theorem rowClear_monomialEquiv_row_eq_one (w : m → Kˣ) (σ : n ≃ m) (r : m)
    (hp : (monomialEquiv (R := K) w σ).val r (σ.symm r) ≠ 0) :
    rowClear (monomialEquiv (R := K) w σ).val r (σ.symm r) hp = 1 := by
  apply rowClear_eq_one_of_forall_ne_zero_eq
  intro i hi
  have h1 : σ (σ.symm r) = i :=
    (monomialEquiv_val_ne_zero_iff w σ i (σ.symm r)).mp hi
  have h2 : σ (σ.symm r) = r := σ.apply_symm_apply r
  exact h1.symm.trans h2

omit [LinearOrder m] in
theorem columnClear_monomialEquiv_row_eq_one (w : m → Kˣ) (σ : n ≃ m) (r : m)
    (hp : (monomialEquiv (R := K) w σ).val r (σ.symm r) ≠ 0) :
    columnClear (monomialEquiv (R := K) w σ).val r (σ.symm r) hp = 1 := by
  apply columnClear_eq_one_of_forall_ne_zero_eq
  intro j hj
  have hEq : σ j = r := (monomialEquiv_val_ne_zero_iff w σ r j).mp hj
  have hEq2 : σ (σ.symm r) = r := σ.apply_symm_apply r
  have : σ j = σ (σ.symm r) := hEq.trans hEq2.symm
  exact σ.injective this

omit [LinearOrder n] in
theorem upperRowClear_monomialEquiv_row_eq_one (w : m → Kˣ) (σ : n ≃ m) (r : m)
    (hp : (monomialEquiv (R := K) w σ).val r (σ.symm r) ≠ 0) :
    upperRowClear (monomialEquiv (R := K) w σ).val r (σ.symm r) hp = 1 := by
  apply upperRowClear_eq_one_of_forall_ne_zero_eq
  intro i hi
  have h1 : σ (σ.symm r) = i :=
    (monomialEquiv_val_ne_zero_iff w σ i (σ.symm r)).mp hi
  have h2 : σ (σ.symm r) = r := σ.apply_symm_apply r
  exact h1.symm.trans h2

omit [LinearOrder m] in
theorem upperColumnClear_monomialEquiv_row_eq_one (w : m → Kˣ) (σ : n ≃ m) (r : m)
    (hp : (monomialEquiv (R := K) w σ).val r (σ.symm r) ≠ 0) :
    upperColumnClear (monomialEquiv (R := K) w σ).val r (σ.symm r) hp = 1 := by
  apply upperColumnClear_eq_one_of_forall_ne_zero_eq
  intro j hj
  have hEq : σ j = r := (monomialEquiv_val_ne_zero_iff w σ r j).mp hj
  have hEq2 : σ (σ.symm r) = r := σ.apply_symm_apply r
  have : σ j = σ (σ.symm r) := hEq.trans hEq2.symm
  exact σ.injective this

end MonomialClear

/-! ### E. Deletion API for heterogeneous monomial equivalences

We work with `monomialEquiv w σ : GeneralLinearEquiv m n K` whose
orientation is

  `val i j = if σ j = i then (w i : K) else 0`.

Thus column `c : n` carries its unique nonzero entry at row `σ c`
with weight `w (σ c)`.  Deleting this pivot gives

* target deletion `DeletedIndex m (σ c)` and source deletion
  `DeletedIndex n c`,
* induced permutation `deletePerm σ c : DeletedIndex n c ≃ DeletedIndex m (σ c)`,
* restricted weights `deleteWeights w (σ c) : DeletedIndex m (σ c) → Kˣ`.

Insertion `insertPerm` and `insertWeights` are the inverse operations.
`deleteEntryEquiv` on the isolated monomial entry coincides with the
monomial built from the deleted data.  Reinsertion via
`insertEntryEquiv` recovers the original monomial; away from the pivot
the entries agree.  Multiplication order is preserved by construction;
no commutativity is used.

Nonclaims: we do not claim Bruhat factors are trivial in this packet;
we do not provide order-isomorphism upgrades or `Finset.erase`
translations beyond the `DeletedIndex` API already in the library.
All side conditions `i ≠ σ c`, `j ≠ c` are proved explicitly. -/

section MonomialDeletePerm

variable {m n : Type*} [DecidableEq m] [DecidableEq n]

/-- Deletion of a pivot from a heterogeneous permutation.

For `σ : n ≃ m` and `c : n`, the induced equivalence
`DeletedIndex n c ≃ DeletedIndex m (σ c)` sends `⟨j, hj⟩` to
`⟨σ j, _⟩`.  The inequality proof uses injectivity of `σ`. -/
def deletePerm (σ : n ≃ m) (c : n) :
    DeletedIndex n c ≃ DeletedIndex m (σ c) where
  toFun j :=
    ⟨σ j.val, fun hEq => j.prop (σ.injective hEq)⟩
  invFun i :=
    ⟨σ.symm i.val, fun hEq => i.prop (by
      calc i.val = σ (σ.symm i.val) := (σ.apply_symm_apply i.val).symm
        _ = σ c := congrArg σ hEq)⟩
  left_inv j := by
    apply Subtype.ext
    exact σ.symm_apply_apply j.val
  right_inv i := by
    apply Subtype.ext
    exact σ.apply_symm_apply i.val

omit [DecidableEq m] [DecidableEq n] in
@[simp]
theorem deletePerm_apply (σ : n ≃ m) (c : n) (j : DeletedIndex n c) :
    (deletePerm σ c j).val = σ j.val := rfl

omit [DecidableEq m] [DecidableEq n] in
@[simp]
theorem deletePerm_symm_apply (σ : n ≃ m) (c : n) (i : DeletedIndex m (σ c)) :
    ((deletePerm σ c).symm i).val = σ.symm i.val := rfl

omit [DecidableEq m] [DecidableEq n] in
theorem deletePerm_apply_eq_iff (σ : n ≃ m) (c : n)
    (j : DeletedIndex n c) (i : DeletedIndex m (σ c)) :
    deletePerm σ c j = i ↔ σ j.val = i.val := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    simpa using this
  · intro h
    apply Subtype.ext
    exact h

/-- Insertion of a pivot into a deleted permutation.

Given `c : n`, `r : m` and `e : DeletedIndex n c ≃ DeletedIndex m r`,
build `n ≃ m` sending `c ↦ r` and `j ≠ c ↦ (e ⟨j, _⟩).val`.
Orientation matches `deletePerm`: column → row via `σ`.

The `toFun`/`invFun` are defined inline via `where` so that `left_inv`/`right_inv`
goals already contain the `if`-branch; each branch is then closed with
`simp only [dite_eq_left/dite_eq_right]`. -/
def insertPerm (c : n) (r : m)
    (e : DeletedIndex n c ≃ DeletedIndex m r) : n ≃ m where
  toFun j := if h : j = c then r else (e ⟨j, h⟩).val
  invFun i := if h : i = r then c else (e.symm ⟨i, h⟩).val
  left_inv := by
    intro j
    by_cases hj : j = c
    · subst j
      change (if h : (if h : c = c then r else (e ⟨c, h⟩).val) = r then c else
          (e.symm ⟨(if h : c = c then r else (e ⟨c, h⟩).val), h⟩).val) = c
      rw [dite_eq_left rfl, dite_eq_left rfl]
    · have hp : (e ⟨j, hj⟩).val ≠ r := (e ⟨j, hj⟩).prop
      simp only [dite_eq_right hj, dite_eq_right hp]
      have hSub : (⟨(e ⟨j, hj⟩).val, hp⟩ : DeletedIndex m r) = e ⟨j, hj⟩ :=
        Subtype.ext rfl
      rw [hSub]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨j, hj⟩)
  right_inv := by
    intro i
    by_cases hi : i = r
    · subst i
      change (if h : (if h : r = r then c else (e.symm ⟨r, h⟩).val) = c then r else
          (e ⟨(if h : r = r then c else (e.symm ⟨r, h⟩).val), h⟩).val) = r
      rw [dite_eq_left rfl, dite_eq_left rfl]
    · have hp : (e.symm ⟨i, hi⟩).val ≠ c := (e.symm ⟨i, hi⟩).prop
      simp only [dite_eq_right hi, dite_eq_right hp]
      have hSub : (⟨(e.symm ⟨i, hi⟩).val, hp⟩ : DeletedIndex n c) = e.symm ⟨i, hi⟩ :=
        Subtype.ext rfl
      rw [hSub]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)

theorem insertPerm_apply_of_eq (c : n) (r : m)
    (e : DeletedIndex n c ≃ DeletedIndex m r) :
    insertPerm c r e c = r := by
  change (if h : c = c then r else (e ⟨c, h⟩).val) = r
  exact dite_eq_left rfl

theorem insertPerm_apply_of_ne (c : n) (r : m)
    (e : DeletedIndex n c ≃ DeletedIndex m r) (j : n) (hj : j ≠ c) :
    insertPerm c r e j = (e ⟨j, hj⟩).val := by
  change (if h : j = c then r else (e ⟨j, h⟩).val) = (e ⟨j, hj⟩).val
  exact dite_eq_right hj

theorem insertPerm_symm_apply_of_eq (c : n) (r : m)
    (e : DeletedIndex n c ≃ DeletedIndex m r) :
    (insertPerm c r e).symm r = c := by
  have h : (insertPerm c r e).symm ((insertPerm c r e) c) = c :=
    (insertPerm c r e).symm_apply_apply c
  rw [insertPerm_apply_of_eq] at h
  exact h

theorem insertPerm_symm_apply_of_ne (c : n) (r : m)
    (e : DeletedIndex n c ≃ DeletedIndex m r) (i : m) (hi : i ≠ r) :
    (insertPerm c r e).symm i = (e.symm ⟨i, hi⟩).val := by
  change (if h : i = r then c else (e.symm ⟨i, h⟩).val) = (e.symm ⟨i, hi⟩).val
  exact dite_eq_right hi

/-- Insertion after deletion recovers the original permutation pointwise. -/
theorem insertPerm_deletePerm_apply (σ : n ≃ m) (c : n) (j : n) :
    insertPerm c (σ c) (deletePerm σ c) j = σ j := by
  by_cases hj : j = c
  · rw [hj, insertPerm_apply_of_eq]
  · rw [insertPerm_apply_of_ne _ _ _ _ hj]
    rfl

/-- Full Equiv equality: inserting the deleted perm recovers `σ`. -/
theorem insertPerm_deletePerm (σ : n ≃ m) (c : n) :
    insertPerm c (σ c) (deletePerm σ c) = σ := by
  apply Equiv.ext
  intro j
  exact insertPerm_deletePerm_apply σ c j

/-- Deletion after insertion recovers the smaller permutation pointwise at the
value level.  The codomain of `deletePerm (insertPerm c r e) c` is
`DeletedIndex m ((insertPerm c r e) c)`, propositionally but not definitionally `r`,
so we state equality of underlying `m` values. -/
theorem deletePerm_insertPerm_apply (c : n) (r : m)
    (e : DeletedIndex n c ≃ DeletedIndex m r) (j : DeletedIndex n c) :
    (deletePerm (insertPerm c r e) c j).val = (e j).val := by
  have hj : j.val ≠ c := j.prop
  have hEq : (insertPerm c r e) j.val = (e ⟨j.val, hj⟩).val := by
    rw [insertPerm_apply_of_ne c r e j.val hj]
  have hSub : (⟨j.val, hj⟩ : DeletedIndex n c) = j := Subtype.ext rfl
  calc (deletePerm (insertPerm c r e) c j).val
      = (insertPerm c r e) j.val := rfl
    _ = (e ⟨j.val, hj⟩).val := hEq
    _ = (e j).val := by rw [hSub]

/-- Full Equiv equality with explicit transport along `insertPerm_apply_of_eq`:
`deletePerm (insertPerm c r e) c` has codomain indexed by `(insertPerm c r e) c`,
so we compose with `deletedIndexEquivOfEq` before comparing to `e`. -/
theorem deletePerm_insertPerm (c : n) (r : m)
    (e : DeletedIndex n c ≃ DeletedIndex m r) :
    (deletePerm (insertPerm c r e) c).trans
        (deletedIndexEquivOfEq (insertPerm_apply_of_eq c r e)) = e := by
  apply Equiv.ext
  intro j
  apply Subtype.ext
  calc ((deletePerm (insertPerm c r e) c).trans
          (deletedIndexEquivOfEq (insertPerm_apply_of_eq c r e)) j).val
      = (deletePerm (insertPerm c r e) c j).val := rfl
    _ = (e j).val := deletePerm_insertPerm_apply c r e j

end MonomialDeletePerm

section MonomialDeleteWeights

variable {m : Type*} [DecidableEq m]
variable {K : Type*} [DivisionRing K]

/-- Deletion/restriction of monomial weights at `r : m`. -/
def deleteWeights (w : m → Kˣ) (r : m) :
    DeletedIndex m r → Kˣ := fun i => w i.val

omit [DecidableEq m] in
@[simp]
theorem deleteWeights_apply (w : m → Kˣ) (r : m) (i : DeletedIndex m r) :
    deleteWeights w r i = w i.val := rfl

omit [DecidableEq m] in
theorem insertWeights_apply_of_eq (r : m) (a : Kˣ) (w' : DeletedIndex m r → Kˣ) :
    insertWeights r a w' r = a := insertWeights_apply_self r a w'

omit [DecidableEq m] in
/-- `deleteWeights` after `insertWeights` is identity. -/
theorem deleteWeights_insertWeights (r : m) (a : Kˣ) (w' : DeletedIndex m r → Kˣ) :
    deleteWeights (insertWeights r a w') r = w' := by
  funext i
  have hi : i.val ≠ r := i.prop
  calc deleteWeights (insertWeights r a w') r i
      = insertWeights r a w' i.val := rfl
    _ = w' ⟨i.val, hi⟩ := by rw [insertWeights_apply_of_ne hi]
    _ = w' i := by
        have hSub : (⟨i.val, hi⟩ : DeletedIndex m r) = i := Subtype.ext rfl
        rw [hSub]

omit [DecidableEq m] in
/-- `insertWeights` after `deleteWeights` recovers the original weights. -/
theorem insertWeights_deleteWeights (w : m → Kˣ) (r : m) :
    insertWeights r (w r) (deleteWeights w r) = w := by
  classical
  funext i
  by_cases hi : i = r
  · rw [hi, insertWeights_apply_of_eq]
  · rw [insertWeights_apply_of_ne hi]
    rfl

end MonomialDeleteWeights

section MonomialDeleteWeightsMap

variable {m : Type*}
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

/-- Pointwise `Units.map` commutes with `deleteWeights`. -/
theorem deleteWeights_map (w : m → Kˣ) (r : m) (i : DeletedIndex m r) (f : K →+* L) :
    Units.map f.toMonoidHom (deleteWeights w r i) =
      deleteWeights (fun j => Units.map f.toMonoidHom (w j)) r i :=
  rfl

/-- Function-level `Units.map` commutes with `deleteWeights`. -/
theorem deleteWeights_map_eq (w : m → Kˣ) (r : m) (f : K →+* L) :
    (fun i => Units.map f.toMonoidHom (deleteWeights w r i)) =
      deleteWeights (fun j => Units.map f.toMonoidHom (w j)) r :=
  rfl

end MonomialDeleteWeightsMap

section MonomialDeleteWeightsMonomialMap

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
variable {K L : Type*} [DivisionRing K] [DivisionRing L]

/-- Mapping a deleted-weight monomial along `f` equals the monomial over mapped deleted weights. -/
theorem monomialEquiv_deleteWeights_map (w : m → Kˣ) (σ : n ≃ m) (c : n) (f : K →+* L) :
    (monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c)).map f =
      monomialEquiv (R := L) (deleteWeights (fun j => Units.map f.toMonoidHom (w j)) (σ c))
        (deletePerm σ c) := by
  rw [map_monomialEquiv]
  exact congrArg (fun w' : DeletedIndex m (σ c) → Lˣ =>
    monomialEquiv (R := L) w' (deletePerm σ c)) (deleteWeights_map_eq w (σ c) f)

end MonomialDeleteWeightsMonomialMap

section MonomialInsertCompat

variable {m n : Type*} [DecidableEq m] [DecidableEq n]
variable {K : Type*} [DivisionRing K]

/-- Alias for the monomial-specific deletion of weights via `σ c`. -/
abbrev monomialDeleteWeights (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    DeletedIndex m (σ c) → Kˣ := deleteWeights w (σ c)

/-- Alias for the monomial-specific `deletePerm`. -/
abbrev monomialDeletePerm (σ : n ≃ m) (c : n) :
    DeletedIndex n c ≃ DeletedIndex m (σ c) := deletePerm σ c

/-- Insertion/deletion compatibility for permutations with explicit transport:
deleting the inserted perm then transporting along `insertPerm_apply_of_eq`
recovers `e`. -/
theorem insertEquiv_deletePerm (c : n) (r : m)
    (e : DeletedIndex n c ≃ DeletedIndex m r) :
    (deletePerm (insertPerm c r e) c).trans
        (deletedIndexEquivOfEq (insertPerm_apply_of_eq c r e)) = e :=
  deletePerm_insertPerm c r e

/-- Insertion/deletion compatibility for permutations: inserting the
deleted permutation recovers `σ`. -/
theorem deletePerm_insertEquiv (σ : n ≃ m) (c : n) :
    insertPerm c (σ c) (deletePerm σ c) = σ :=
  insertPerm_deletePerm σ c

omit [DecidableEq m] in
/-- Insertion/deletion compatibility for weights (API-native name:
`insertWeights_deleteWeights`). -/
theorem insertWeights_deleteWeights_compat (r : m) (a : Kˣ)
    (w' : DeletedIndex m r → Kˣ) :
    deleteWeights (insertWeights r a w') r = w' :=
  deleteWeights_insertWeights r a w'

omit [DecidableEq m] in
theorem deleteWeights_insertWeights_compat (w : m → Kˣ) (r : m) :
    insertWeights r (w r) (deleteWeights w r) = w :=
  insertWeights_deleteWeights w r

end MonomialInsertCompat

section MonomialDeleteEntryEquiv

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n]
variable {K : Type*} [DivisionRing K]

omit [LinearOrder m] [LinearOrder n] in
/-- The monomial matrix is isolated at its pivot `(σ c, c)`. -/
theorem isIsolatedEntry_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    IsolatedEntry (monomialEquiv (R := K) w σ) (σ c) c where
  row_zero j hj := by
    have hNe : σ j ≠ σ c := fun hEq => hj (σ.injective hEq)
    exact monomialEquiv_val_zero_of_row_ne (K := K) w σ hNe
  col_zero i hi := by
    exact monomialEquiv_val_zero_of_col_ne (K := K) w σ hi

omit [LinearOrder m] [LinearOrder n] in
theorem isolatedPivotUnit_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    isolatedPivotUnit (isIsolatedEntry_monomialEquiv w σ c) = w (σ c) := by
  apply Units.ext
  have hVal : (monomialEquiv (R := K) w σ).val (σ c) c = (w (σ c) : K) := by
    rw [val_monomialEquiv_apply, ite_eq_left rfl]
  calc ((isolatedPivotUnit (isIsolatedEntry_monomialEquiv w σ c)).val : K)
      = (monomialEquiv (R := K) w σ).val (σ c) c := rfl
    _ = (w (σ c) : K) := hVal

omit [LinearOrder m] [LinearOrder n] in
/-- Deletion of the isolated pivot entry from a monomial equivalence coincides
with the monomial built from restricted weights and deleted permutation.

Orientation: column `c` and row `σ c` are deleted; the induced permutation
is `deletePerm σ c` sending deleted columns to deleted rows. -/
theorem deleteEntryEquiv_monomialEquiv_eq (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    deleteEntryEquiv (isIsolatedEntry_monomialEquiv w σ c) =
      monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c) := by
  apply GeneralLinearEquiv.ext
  ext i j
  have hBase : (deleteEntryEquiv (isIsolatedEntry_monomialEquiv w σ c)).val i j =
      (monomialEquiv (R := K) w σ).val i.val j.val := rfl
  rw [hBase, val_monomialEquiv_apply, val_monomialEquiv_apply]
  by_cases hEq : σ j.val = i.val
  · have hPermEq : deletePerm σ c j = i := Subtype.ext hEq
    rw [ite_eq_left hEq, ite_eq_left hPermEq, deleteWeights_apply]
  · have hPermNe : deletePerm σ c j ≠ i :=
      fun hContra => hEq (congrArg Subtype.val hContra)
    rw [ite_eq_right hEq, ite_eq_right hPermNe]

omit [LinearOrder m] [LinearOrder n] in
/-- Entrywise identification away from the pivot. -/
theorem deleteEntryEquiv_monomialEquiv_entry_eq (w : m → Kˣ) (σ : n ≃ m) (c : n)
    (i : m) (hi : i ≠ σ c) (j : n) (hj : j ≠ c) :
    (monomialEquiv (R := K) w σ).val i j =
      (monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c)).val
        ⟨i, hi⟩ ⟨j, hj⟩ := by
  have hDel := deleteEntryEquiv_monomialEquiv_eq w σ c
  calc (monomialEquiv (R := K) w σ).val i j
      = (deleteEntryEquiv (isIsolatedEntry_monomialEquiv w σ c)).val ⟨i, hi⟩ ⟨j, hj⟩ := rfl
    _ = (monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c)).val ⟨i, hi⟩ ⟨j, hj⟩ := by
        rw [hDel]

omit [LinearOrder m] [LinearOrder n] in
/-- Reinsertion: putting the deleted monomial data back via `insertEntryEquiv`
recovers the original monomial equivalence.

This uses `insert_delete_reconstruction` together with the exact
deleted-data identification and pivot-unit lemma above. -/
theorem insertEntryEquiv_monomialDeleteEquiv (w : m → Kˣ) (σ : n ≃ m) (c : n) :
    insertEntryEquiv (σ c) c (w (σ c))
      (monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c)) =
      monomialEquiv (R := K) w σ := by
  have hIso : IsolatedEntry (monomialEquiv (R := K) w σ) (σ c) c :=
    isIsolatedEntry_monomialEquiv w σ c
  have hUnit : isolatedPivotUnit hIso = w (σ c) :=
    isolatedPivotUnit_monomialEquiv w σ c
  have hDel : deleteEntryEquiv hIso =
      monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c) :=
    deleteEntryEquiv_monomialEquiv_eq w σ c
  calc insertEntryEquiv (σ c) c (w (σ c))
        (monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c))
      = insertEntryEquiv (σ c) c (isolatedPivotUnit hIso) (deleteEntryEquiv hIso) := by
        rw [← hUnit, ← hDel]
    _ = monomialEquiv (R := K) w σ := insert_delete_reconstruction hIso

omit [LinearOrder m] [LinearOrder n] in
/-- Entrywise version of reinsertion away from the pivot. -/
theorem insertEntryEquiv_monomialEquiv_away (w : m → Kˣ) (σ : n ≃ m) (c : n)
    (i : m) (_ : i ≠ σ c) (j : n) (_ : j ≠ c) :
    (insertEntryEquiv (σ c) c (w (σ c))
      (monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c))).val i j =
      (monomialEquiv (R := K) w σ).val i j := by
  rw [insertEntryEquiv_monomialDeleteEquiv w σ c]

end MonomialDeleteEntryEquiv

section CanonicalPivotMonomialFixedPoint

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n] [Nonempty n]
variable {K : Type*} [DivisionRing K]

/-- Monomial equivalences are fixed by canonical pivot clearing.

The canonical pivot row of `monomialEquiv w σ` is `σ canonicalColumn`,
its column support is the singleton `{σ canonicalColumn}` and its row
support is `{canonicalColumn}`; hence both the upper row and column
clearing factors are identity and `canonicalPivotCleared` is the identity
on the monomial. -/
theorem canonicalPivotCleared_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) :
    canonicalPivotCleared (monomialEquiv (R := K) w σ) =
      monomialEquiv (R := K) w σ := by
  set e : GeneralLinearEquiv m n K := monomialEquiv (R := K) w σ with he
  set c : n := (canonicalColumn : n) with hc
  have hRowEq : canonicalPivotRow e = σ c := canonicalPivotRow_monomialEquiv w σ
  have hRowClear : rowClear e.val (canonicalPivotRow e) c (canonicalPivotRow_ne_zero e) = 1 := by
    apply rowClear_eq_one_of_forall_ne_zero_eq
    intro i hi
    have hσ : σ c = i := (monomialEquiv_val_ne_zero_iff w σ i c).mp hi
    calc i = σ c := hσ.symm
      _ = canonicalPivotRow e := hRowEq.symm
  have hColClear : columnClear e.val (canonicalPivotRow e) c (canonicalPivotRow_ne_zero e) = 1 := by
    apply columnClear_eq_one_of_forall_ne_zero_eq
    intro j hj
    have hσ : σ j = canonicalPivotRow e :=
      (monomialEquiv_val_ne_zero_iff w σ (canonicalPivotRow e) j).mp hj
    have hσc : σ j = σ c := hσ.trans hRowEq
    exact σ.injective hσc
  apply GeneralLinearEquiv.ext
  -- `canonicalPivotCleared` is `pivotClearedEquiv` at the canonical row/col
  have hVal : (canonicalPivotCleared e).val =
      pivotClearedMatrix e.val (canonicalPivotRow e) c (canonicalPivotRow_ne_zero e) := rfl
  rw [hVal]
  -- unfold clearing product and use identity factors
  calc pivotClearedMatrix e.val (canonicalPivotRow e) c (canonicalPivotRow_ne_zero e)
      = ((rowClear e.val (canonicalPivotRow e) c (canonicalPivotRow_ne_zero e) : GL m K) :
          Matrix m m K) * e.val *
          ((columnClear e.val (canonicalPivotRow e) c (canonicalPivotRow_ne_zero e) : GL n K) :
            Matrix n n K) := rfl
    _ = ((1 : GL m K) : Matrix m m K) * e.val * ((1 : GL n K) : Matrix n n K) := by
        rw [hRowClear, hColClear]
    _ = e.val := by simp

end CanonicalPivotMonomialFixedPoint

section ReducedPivotMonomialEquiv

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]
  [LinearOrder m] [LinearOrder n] [Nonempty n]
variable {K : Type*} [DivisionRing K]

/-- After canonical pivot clearing a monomial equivalence, its reduced pivot
equivalence, reindexed along the equality of the canonical pivot row with
`σ canonicalColumn`, is the monomial equivalence built from `deleteWeights`
and `deletePerm`.

Orientation fix: `canonicalPivotRow_monomialEquiv` proves
`canonicalPivotRow (monomialEquiv w σ) = σ canonicalColumn`.  The reindex
needs `DeletedIndex m (σ c) ≃ DeletedIndex m (canonicalPivotRow _)`,
i.e. the symmetric equality, which is `.symm` of the stated helper.
The task statement therefore type-checks with `.symm`; this is the only
adjustment beyond `(R := K)`.

Uses the fixed-point `canonicalPivotCleared_monomialEquiv`, `val_reindex`,
and a direct entrywise argument via `val_monomialEquiv_apply` and
`deletePerm_apply_eq_iff`.  No case split on `Fintype.card n`; the empty
`DeletedIndex` case is uniform because `submatrix` and `monomialEquiv` handle vacuous indices. -/
theorem reducedPivotEquiv_monomialEquiv (w : m → Kˣ) (σ : n ≃ m) :
    (reducedPivotEquiv (monomialEquiv (R := K) w σ)).reindex
      (deletedIndexEquivOfEq (canonicalPivotRow_monomialEquiv (K := K) w σ).symm)
      (Equiv.refl (DeletedIndex n (canonicalColumn : n))) =
    monomialEquiv (R := K) (deleteWeights w (σ (canonicalColumn : n)))
      (deletePerm σ (canonicalColumn : n)) := by
  set e : GeneralLinearEquiv m n K := monomialEquiv (R := K) w σ with he_def
  set c : n := (canonicalColumn : n) with hc_def
  have hRow : canonicalPivotRow e = σ c :=
    canonicalPivotRow_monomialEquiv (K := K) w σ
  have hClear : canonicalPivotCleared e = e :=
    canonicalPivotCleared_monomialEquiv (K := K) w σ
  have hClearVal : (canonicalPivotCleared e).val = e.val := by rw [hClear]
  apply GeneralLinearEquiv.ext
  ext i j
  calc ((reducedPivotEquiv e).reindex (deletedIndexEquivOfEq hRow.symm)
          (Equiv.refl (DeletedIndex n c))).val i j
      = (reducedPivotEquiv e).val ((deletedIndexEquivOfEq hRow.symm) i)
          ((Equiv.refl (DeletedIndex n c)) j) := by
        simp [val_reindex, Matrix.submatrix_apply]
    _ = (canonicalPivotCleared e).val ((deletedIndexEquivOfEq hRow.symm) i).val
          (((Equiv.refl (DeletedIndex n c)) j).val) := rfl
    _ = e.val ((deletedIndexEquivOfEq hRow.symm) i).val
          (((Equiv.refl (DeletedIndex n c)) j).val) := by rw [hClearVal]
    _ = e.val i.val j.val := rfl
    _ = (monomialEquiv (R := K) (deleteWeights w (σ c)) (deletePerm σ c)).val i j := by
        rw [val_monomialEquiv_apply, val_monomialEquiv_apply]
        by_cases hEq : σ j.val = i.val
        · have hPerm : deletePerm σ c j = i := by
            rw [deletePerm_apply_eq_iff]
            exact hEq
          rw [ite_eq_left hEq, ite_eq_left hPerm]
          rfl
        · have hPermNe : deletePerm σ c j ≠ i := by
            intro hContra
            have : σ j.val = i.val :=
              (deletePerm_apply_eq_iff σ c j i).mp hContra
            exact hEq this
          rw [ite_eq_right hEq, ite_eq_right hPermNe]

end ReducedPivotMonomialEquiv

end GeneralLinearEquiv

end Matrix
