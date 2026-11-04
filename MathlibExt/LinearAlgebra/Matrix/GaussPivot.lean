/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

import Mathlib.Data.Finset.Sort

/-!
# Gaussian elimination with row pivots

This file constructs unit lower-triangular row operations for a pivot step and proves that a row
permutation followed by such operations puts every finite matrix over a field in row echelon form.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted

private theorem gaussPivot_elimStep
    {K m n : Type*} [Field K] [Fintype m] [DecidableEq m] [LinearOrder m]
    (A : Matrix m n K) (r : m) (j : n) (i₀ : m) (h : A i₀ j ≠ 0) :
    ∃ P : Matrix m m K, P.IsLowerTriangular ∧ (∀ i, P.diag i = 1) ∧
      ∀ i > r, (P * A.submatrix (Equiv.swap r i₀) id) i j = 0 := by
  let A' := A.submatrix (Equiv.swap r i₀) id
  let P : Matrix m m K := fun i k =>
    (if i = k then 1 else 0) -
      if k = r ∧ r < i then A' i j / A' r j else 0
  have hpivot : A' r j ≠ 0 := by
    simpa [A'] using h
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i k hik
    have hne : i ≠ k := ne_of_lt hik
    have hnot : ¬(k = r ∧ r < i) := by
      rintro ⟨rfl, hri⟩
      exact lt_asymm hik hri
    simp [P, hne, hnot]
  · intro i
    have hnot : ¬(i = r ∧ r < i) := by
      rintro ⟨rfl, hri⟩
      exact lt_irrefl _ hri
    change P i i = 1
    simp [P, hnot]
  · intro i hri
    change (P * A') i j = 0
    rw [Matrix.mul_apply]
    change (∑ k, ((if i = k then 1 else 0) -
      if k = r ∧ r < i then A' i j / A' r j else 0) * A' k j) = 0
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    simp [hri, hpivot]

private def gaussPivotLiftPerm {p : ℕ} (τ : Equiv.Perm (Fin p)) :
    Equiv.Perm (Fin (p + 1)) where
  toFun := Fin.cases 0 fun i => (τ i).succ
  invFun := Fin.cases 0 fun i => (τ.symm i).succ
  left_inv i := by
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · simp

@[simp] private theorem gaussPivotLiftPerm_zero {p : ℕ} (τ : Equiv.Perm (Fin p)) :
    gaussPivotLiftPerm τ 0 = 0 := rfl

@[simp] private theorem gaussPivotLiftPerm_succ {p : ℕ} (τ : Equiv.Perm (Fin p))
    (i : Fin p) : gaussPivotLiftPerm τ i.succ = (τ i).succ := rfl

private theorem gaussPivot_isRowEchelon_of_zeroFirstColumn
    {K : Type*} [Zero K] {p q : ℕ} {A : Matrix (Fin p) (Fin (q + 1)) K}
    (hzero : ∀ i, A i 0 = 0) (htail : (A.submatrix id Fin.succ).IsRowEchelon) :
    A.IsRowEchelon := by
  intro i₁ i₂ hi j₂ hleft
  cases j₂ using Fin.cases with
  | zero => exact hzero i₂
  | succ j =>
      apply htail hi
      intro k hk
      exact hleft k.succ (Fin.succ_lt_succ_iff.mpr hk)

private theorem gaussPivot_isRowEchelon_of_pivot
    {K : Type*} [Zero K] {p q : ℕ} {A : Matrix (Fin (p + 1)) (Fin (q + 1)) K}
    (hpivot : A 0 0 ≠ 0) (hzero : ∀ i : Fin p, A i.succ 0 = 0)
    (htail : (A.submatrix Fin.succ Fin.succ).IsRowEchelon) : A.IsRowEchelon := by
  intro i₁ i₂ hi j₂ hleft
  cases i₁ using Fin.cases with
  | zero =>
      cases j₂ using Fin.cases with
      | zero =>
          have hi₂ : 0 < i₂ := hi
          obtain ⟨i₂, rfl⟩ := Fin.eq_succ_of_ne_zero (by omega : i₂ ≠ 0)
          exact hzero i₂
      | succ j =>
          exact (hpivot (hleft 0 (Fin.succ_pos j))).elim
  | succ i₁ =>
      cases i₂ using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hi).elim
      | succ i₂ =>
          cases j₂ using Fin.cases with
          | zero => exact hzero i₂
          | succ j =>
              apply htail (Fin.succ_lt_succ_iff.mp hi)
              intro k hk
              exact hleft k.succ (Fin.succ_lt_succ_iff.mpr hk)

private def gaussPivotHasDecomposition {K : Type*} [Semiring K] {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) K) : Prop :=
  ∃ (L : Matrix (Fin p) (Fin p) K) (σ : Equiv.Perm (Fin p)),
    L.IsLowerTriangular ∧ (∀ i, L.diag i = 1) ∧
      (L * A.submatrix σ id).IsRowEchelon

private theorem gaussPivot_hasDecomposition_of_zeroFirstColumn
    {K : Type*} [Field K] {p q : ℕ} (A : Matrix (Fin p) (Fin (q + 1)) K)
    (hzero : ∀ i, A i 0 = 0)
    (htail : gaussPivotHasDecomposition (A.submatrix id Fin.succ)) :
    gaussPivotHasDecomposition A := by
  obtain ⟨L, σ, hL, hdiag, hechelon⟩ := htail
  refine ⟨L, σ, hL, hdiag, gaussPivot_isRowEchelon_of_zeroFirstColumn ?_ ?_⟩
  · intro i
    rw [Matrix.mul_apply]
    simp [hzero]
  · have heq :
        (L * A.submatrix σ id).submatrix id Fin.succ =
          L * (A.submatrix id Fin.succ).submatrix σ id := by
      ext i j
      simp [Matrix.mul_apply]
    rw [heq]
    exact hechelon

private def gaussPivotBorderLower {K : Type*} [Zero K] [One K] {p : ℕ}
    (d : Fin p → K) (L₀ : Matrix (Fin p) (Fin p) K) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) K :=
  Fin.cases (Fin.cases 1 fun _ => 0) fun i => Fin.cases (d i) fun j => L₀ i j

private theorem gaussPivotBorderLower_isLowerTriangular
    {K : Type*} [Zero K] [One K] {p : ℕ} {d : Fin p → K}
    {L₀ : Matrix (Fin p) (Fin p) K} (hL₀ : L₀.IsLowerTriangular) :
    (gaussPivotBorderLower d L₀).IsLowerTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j => simp [gaussPivotBorderLower]
  | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ j => exact hL₀ (Fin.succ_lt_succ_iff.mp hij)

private theorem gaussPivotBorderLower_diag
    {K : Type*} [Zero K] [One K] {p : ℕ} {d : Fin p → K}
    {L₀ : Matrix (Fin p) (Fin p) K} (hdiag : ∀ i, L₀.diag i = 1) :
    ∀ i, (gaussPivotBorderLower d L₀).diag i = 1 := by
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => exact hdiag i

private theorem gaussPivotBorderLower_mul_zero
    {K : Type*} [Semiring K] {p : ℕ} (d : Fin p → K)
    (L₀ : Matrix (Fin p) (Fin p) K) {n : Type*}
    (B : Matrix (Fin (p + 1)) n K) (j : n) :
    (gaussPivotBorderLower d L₀ * B) 0 j = B 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [gaussPivotBorderLower]

private theorem gaussPivotBorderLower_mul_succ
    {K : Type*} [Semiring K] {p : ℕ} (d : Fin p → K)
    (L₀ : Matrix (Fin p) (Fin p) K) {n : Type*}
    (B : Matrix (Fin (p + 1)) n K) (i : Fin p) (j : n) :
    (gaussPivotBorderLower d L₀ * B) i.succ j =
      d i * B 0 j + ∑ k, L₀ i k * B k.succ j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [gaussPivotBorderLower]

private theorem gaussPivot_hasDecomposition_of_pivot
    {K : Type*} [Field K] {p q : ℕ}
    (A : Matrix (Fin (p + 1)) (Fin (q + 1)) K) (i₀ : Fin (p + 1))
    (hi₀ : A i₀ 0 ≠ 0)
    (ih : ∀ D : Matrix (Fin p) (Fin q) K, gaussPivotHasDecomposition D) :
    gaussPivotHasDecomposition A := by
  let A' := A.submatrix (Equiv.swap 0 i₀) id
  have hpivot : A' 0 0 ≠ 0 := by
    simpa [A'] using hi₀
  let c : Fin p → K := fun i => A' i.succ 0 / A' 0 0
  let D : Matrix (Fin p) (Fin q) K := fun i j =>
    A' i.succ j.succ - c i * A' 0 j.succ
  obtain ⟨L₀, τ, hL₀, hdiag₀, hechelon₀⟩ := ih D
  let d : Fin p → K := fun i => -∑ k, L₀ i k * c (τ k)
  let L := gaussPivotBorderLower d L₀
  let σ := (gaussPivotLiftPerm τ).trans (Equiv.swap 0 i₀)
  refine ⟨L, σ, gaussPivotBorderLower_isLowerTriangular hL₀,
    gaussPivotBorderLower_diag hdiag₀, ?_⟩
  apply gaussPivot_isRowEchelon_of_pivot
  · change (gaussPivotBorderLower d L₀ * A.submatrix σ id) 0 0 ≠ 0
    rw [gaussPivotBorderLower_mul_zero]
    simpa [σ, A'] using hpivot
  · intro i
    change (gaussPivotBorderLower d L₀ * A.submatrix σ id) i.succ 0 = 0
    rw [gaussPivotBorderLower_mul_succ]
    change d i * A' 0 0 + ∑ k, L₀ i k * A' (τ k).succ 0 = 0
    have hsum :
        (∑ k, L₀ i k * c (τ k)) * A' 0 0 =
          ∑ k, L₀ i k * A' (τ k).succ 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp [c, mul_assoc, hpivot]
    simp only [d, neg_mul]
    rw [hsum, neg_add_cancel]
  · have heq :
        (L * A.submatrix σ id).submatrix Fin.succ Fin.succ =
          L₀ * D.submatrix τ id := by
      ext i j
      change (gaussPivotBorderLower d L₀ * A.submatrix σ id) i.succ j.succ =
        (L₀ * D.submatrix τ id) i j
      rw [gaussPivotBorderLower_mul_succ, Matrix.mul_apply]
      change d i * A' 0 j.succ + ∑ k, L₀ i k * A' (τ k).succ j.succ =
        ∑ k, L₀ i k * (A' (τ k).succ j.succ - c (τ k) * A' 0 j.succ)
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
      rw [← Finset.sum_mul]
      simp [d]
      ring
    rw [heq]
    exact hechelon₀

private theorem gaussPivot_finHasDecomposition
    {K : Type*} [Field K] {p q : ℕ} (A : Matrix (Fin p) (Fin q) K) :
    gaussPivotHasDecomposition A := by
  induction q generalizing p with
  | zero =>
      refine ⟨1, Equiv.refl _, Matrix.blockTriangular_one, ?_, ?_⟩
      · intro i
        simp
      · intro i₁ i₂ hi j₂
        exact Fin.elim0 j₂
  | succ q ih =>
      cases p with
      | zero =>
          refine ⟨1, Equiv.refl _, Matrix.blockTriangular_one, ?_, ?_⟩
          · intro i
            exact Fin.elim0 i
          · intro i₁
            exact Fin.elim0 i₁
      | succ p =>
          by_cases hzero : ∀ i, A i 0 = 0
          · exact gaussPivot_hasDecomposition_of_zeroFirstColumn A hzero (ih _)
          · obtain ⟨i₀, hi₀⟩ := not_forall.mp hzero
            exact gaussPivot_hasDecomposition_of_pivot A i₀ hi₀ fun D => ih D

private theorem gaussPivot_isRowEchelon_of_submatrix_orderIso
    {K r c m n : Type*} [Zero K] [LinearOrder r] [LinearOrder c]
    [LinearOrder m] [LinearOrder n] (er : r ≃o m) (ec : c ≃o n)
    {A : Matrix m n K} (hA : (A.submatrix er ec).IsRowEchelon) : A.IsRowEchelon := by
  intro i₁ i₂ hi j₂ hleft
  have hi' : er.symm i₁ < er.symm i₂ := by
    simpa using hi
  have hzero := hA hi' (j₂ := ec.symm j₂) fun j₁ hj₁ => by
    have hj₁' : ec j₁ < j₂ := by
      simpa only [ec.apply_symm_apply] using (ec.lt_iff_lt.mpr hj₁)
    simpa only [Matrix.submatrix_apply, er.apply_symm_apply] using hleft (ec j₁) hj₁'
  simpa using hzero

/-- **Row echelon form via a row permutation and a unit lower-triangular matrix.** Let $K$ be a
field and let $A$ be a matrix over $K$ whose rows and columns are indexed by finite linearly
ordered sets. Then there are a permutation $\sigma$ of the row indices and a square matrix $L$ over
$K$ indexed by the row indices, lower triangular with every diagonal entry equal to $1$, such that
the matrix $L A_\sigma$ is in row echelon form. Here $A_\sigma$ is the matrix with entries
$(A_\sigma)_{ic} = A_{\sigma(i) c}$, and a matrix $B$ is in row echelon form when for all rows
$i_1 < i_2$ and every column $c$, if $B_{i_1 c'} = 0$ for every column $c' < c$, then
$B_{i_2 c} = 0$. -/
theorem _root_.Matrix.exists_unitLowerTriangular_mul_submatrix_isRowEchelon
    {K m n : Type*} [Field K] [Fintype m] [LinearOrder m]
    [Finite n] [LinearOrder n] (A : Matrix m n K) :
    ∃ (L : Matrix m m K) (σ : Equiv.Perm m),
      L.IsLowerTriangular ∧ (∀ i, L.diag i = 1) ∧
        (L * A.submatrix σ id).IsRowEchelon := by
  let _ : Fintype n := Fintype.ofFinite n
  let em : Fin (Fintype.card m) ≃o m := Fintype.orderIsoFinOfCardEq m rfl
  let en : Fin (Fintype.card n) ≃o n := Fintype.orderIsoFinOfCardEq n rfl
  let A₀ := A.submatrix em en
  obtain ⟨L₀, σ₀, hL₀, hdiag₀, hechelon₀⟩ := gaussPivot_finHasDecomposition A₀
  let L := L₀.submatrix em.symm em.symm
  let σ : Equiv.Perm m := em.symm.toEquiv.trans (σ₀.trans em.toEquiv)
  refine ⟨L, σ, ?_, ?_, ?_⟩
  · intro i j hij
    change L₀ (em.symm i) (em.symm j) = 0
    apply hL₀
    simpa using hij
  · intro i
    change L₀.diag (em.symm i) = 1
    exact hdiag₀ _
  · apply gaussPivot_isRowEchelon_of_submatrix_orderIso em en
    have heq :
        (L * A.submatrix σ id).submatrix em en =
          L₀ * A₀.submatrix σ₀ id := by
      rw [Matrix.submatrix_mul L (A.submatrix σ id) em em en em.bijective]
      ext i j
      simp [L, A₀, σ, Matrix.submatrix_submatrix, Matrix.mul_apply, Function.comp_apply]
    rw [heq]
    exact hechelon₀

variable {K : Type*} [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m]
variable [Fintype n] [DecidableEq n] [LinearOrder n]

/--
**One pivot step of Gaussian elimination.** Let $K$ be a field and let $A$ be a matrix over $K$
whose rows and columns are indexed by finite linearly ordered sets. Let $r$ and $i_0$ be row
indices and $j$ a column index with $A_{i_0 j} \ne 0$, and let $A'$ be the matrix obtained from
$A$ by exchanging rows $r$ and $i_0$. Then there is a square matrix $P$ over $K$ indexed by the
row indices, lower triangular with every diagonal entry equal to $1$, such that
$(P A')_{i j} = 0$ for every row $i > r$.

The row $i_0$ may be any row with a nonzero entry in column $j$; this is not
magnitude-maximizing partial pivoting.

Proves `Wanted` entry `gauss_pivot_elim_step`.

Proof: Use an entrywise unit lower-triangular matrix whose pivot column contains the elimination
coefficients, then evaluate the matrix product as a finite sum (row operations of type 3,
https://en.wikipedia.org/wiki/Gaussian_elimination).

Sources: Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear
inequalities / Gauss's pivot; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997),
Lectures 20-21.
-/
theorem gauss_pivot_elim_step (A : Matrix m n K) (r : m) (j : n)
    (i₀ : m) (h : A i₀ j ≠ 0) :
    ∃ P : Matrix m m K, P.IsLowerTriangular ∧ (∀ i, P.diag i = 1) ∧
      ∀ i > r, (P * A.submatrix (Equiv.swap r i₀) id) i j = 0 := by
  exact gaussPivot_elimStep A r j i₀ h

/--
**Gaussian elimination as a product of row operations.** Let $K$ be a field and let $A$ be a
matrix over $K$ whose rows and columns are indexed by finite linearly ordered sets. Then there
are a permutation $\sigma$ of the row indices and a finite, possibly empty, list
$M_1, \dots, M_\ell$ of square matrices over $K$ indexed by the row indices, each lower
triangular with every diagonal entry equal to $1$, such that the matrix
$M_1 M_2 \cdots M_\ell A_\sigma$ is in row echelon form. Here $A_\sigma$ is the matrix with
entries $(A_\sigma)_{ic} = A_{\sigma(i) c}$, the empty product is the identity matrix, and a
matrix $B$ is in row echelon form when for all rows $i_1 < i_2$ and every column $c$, if
$B_{i_1 c'} = 0$ for every column $c' < c$, then $B_{i_2 c} = 0$.

This records the factorization, not the intermediate matrices of an algorithm trace.

Proves `Wanted` entry `exists_gauss_elimination_opList`.

Proof: Induct on the columns after identifying the ordered index sets with initial segments of
the natural numbers; a nonzero first column uses a row pivot and recurses on the lower-right
block. Package the resulting single unit lower-triangular matrix as a one-element list (forward
elimination to row echelon form, https://en.wikipedia.org/wiki/Gaussian_elimination).

Sources: Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear
inequalities / Gauss's pivot; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM (1997),
Lectures 20-21.
-/
theorem exists_gauss_elimination_opList (A : Matrix m n K) :
    ∃ (ops : List (Matrix m m K)) (σ : Equiv.Perm m),
      (∀ M ∈ ops, M.IsLowerTriangular ∧ ∀ i, M.diag i = 1) ∧
      (ops.prod * A.submatrix σ id).IsRowEchelon := by
  obtain ⟨L, σ, hL, hdiag, hechelon⟩ :=
    Matrix.exists_unitLowerTriangular_mul_submatrix_isRowEchelon A
  refine ⟨[L], σ, ?_, ?_⟩
  · intro M hM
    simp only [List.mem_singleton] at hM
    subst M
    exact ⟨hL, hdiag⟩
  · simpa using hechelon

end MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted
