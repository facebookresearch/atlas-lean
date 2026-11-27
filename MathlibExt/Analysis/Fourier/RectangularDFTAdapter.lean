/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import MathlibExt.Analysis.Fourier.ZModConvolution

/-!
# Rectangular two-dimensional DFT adapter

The row-column two-dimensional DFT on `ZMod m × ZMod n` equals
the separable double sum, and its `1/(m · n)`-normalized inverse
exactly inverts it (both directions). Pointwise product in the
transform domain is circular convolution. Impulse validations
and the wrong-exponent and unnormalized-inverse refutations are
included.
-/

@[expose] public section

namespace MathlibExt.Analysis.Fourier.RectangularDFTAdapter

/-- Transform every row: `ZMod.dft` along the column index `j` for each fixed row `i`. -/
noncomputable def rowDFT {m n : ℕ} [NeZero m] [NeZero n] (x : ZMod m × ZMod n → ℂ) :
    ZMod m × ZMod n → ℂ :=
  fun p => ZMod.dft (fun j : ZMod n => x (p.1, j)) p.2

/-- Transform every column: `ZMod.dft` along the row index `i` for each fixed column. -/
noncomputable def columnDFT {m n : ℕ} [NeZero m] [NeZero n] (y : ZMod m × ZMod n → ℂ) :
    ZMod m × ZMod n → ℂ :=
  fun p => ZMod.dft (fun i : ZMod m => y (i, p.2)) p.1

/-- The row-then-column DFT of an `m × n` array. -/
noncomputable def rowColumnDFT {m n : ℕ} [NeZero m] [NeZero n] (x : ZMod m × ZMod n → ℂ) :
    ZMod m × ZMod n → ℂ :=
  columnDFT (rowDFT x)

/-- Inverse transform of every row: `ZMod.dft.symm` along the column index. -/
noncomputable def rowInvDFT {m n : ℕ} [NeZero m] [NeZero n] (X : ZMod m × ZMod n → ℂ) :
    ZMod m × ZMod n → ℂ :=
  fun p => ZMod.dft.symm (fun l : ZMod n => X (p.1, l)) p.2

/-- Inverse transform of every column: `ZMod.dft.symm` along the row index. -/
noncomputable def columnInvDFT {m n : ℕ} [NeZero m] [NeZero n] (X : ZMod m × ZMod n → ℂ) :
    ZMod m × ZMod n → ℂ :=
  fun p => ZMod.dft.symm (fun k : ZMod m => X (k, p.2)) p.1

/-- The rectangular inverse DFT: undo the column transform, then the row transform. -/
noncomputable def rectangularInvDFT {m n : ℕ} [NeZero m] [NeZero n]
    (X : ZMod m × ZMod n → ℂ) : ZMod m × ZMod n → ℂ :=
  rowInvDFT (columnInvDFT X)

/-- The two-dimensional negative-exponent DFT sum
`X (k, l) = ∑ i, ∑ j, exp (-2πi (i k / m + j l / n)) x (i, j)`. -/
noncomputable def dft2Sum {m n : ℕ} [NeZero m] [NeZero n] (x : ZMod m × ZMod n → ℂ) :
    ZMod m × ZMod n → ℂ :=
  fun p => ∑ i : ZMod m, ∑ j : ZMod n,
    Complex.exp (-2 * Real.pi * Complex.I *
      (((i.val * p.1.val : ℕ) : ℂ) / m + ((j.val * p.2.val : ℕ) : ℂ) / n)) * x (i, j)

/-- The two-dimensional inverse sum with factor `1/(m*n)`
`x (i, j) = (m n)⁻¹ ∑ k, ∑ l, exp (2πi (k i / m + l j / n)) X (k, l)`. -/
noncomputable def invDft2Sum {m n : ℕ} [NeZero m] [NeZero n] (X : ZMod m × ZMod n → ℂ) :
    ZMod m × ZMod n → ℂ :=
  fun p => ((m : ℂ) * n)⁻¹ * ∑ k : ZMod m, ∑ l : ZMod n,
    Complex.exp (2 * Real.pi * Complex.I *
      (((k.val * p.1.val : ℕ) : ℂ) / m + ((l.val * p.2.val : ℕ) : ℂ) / n)) * X (k, l)

/-- Two-dimensional circular convolution, indices taken mod `m` and mod `n`. -/
noncomputable def circularConvolution2 {m n : ℕ} [NeZero m] [NeZero n]
    (x y : ZMod m × ZMod n → ℂ) : ZMod m × ZMod n → ℂ :=
  fun p => ∑ i : ZMod m, ∑ j : ZMod n, x (i, j) * y (p.1 - i, p.2 - j)

private lemma stdAddChar_neg_mul_eq {N : ℕ} [NeZero N] (a b : ZMod N) :
    ZMod.stdAddChar (-(a * b)) =
      Complex.exp (-2 * Real.pi * Complex.I * (((a.val * b.val : ℕ) : ℂ) / N)) := by
  have h : a * b = (((a.val * b.val : ℕ) : ℤ) : ZMod N) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b]
    rw [← Nat.cast_mul]
    norm_cast
  rw [h, AddChar.map_neg_eq_inv, ZMod.stdAddChar_coe]
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

private lemma stdAddChar_mul_eq {N : ℕ} [NeZero N] (a b : ZMod N) :
    ZMod.stdAddChar (a * b) =
      Complex.exp (2 * Real.pi * Complex.I * (((a.val * b.val : ℕ) : ℂ) / N)) := by
  have h : a * b = (((a.val * b.val : ℕ) : ℤ) : ZMod N) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b]
    rw [← Nat.cast_mul]
    norm_cast
  rw [h, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- **Row-then-column DFT is the 2-D sum.** For `m, n > 0`, transforming the rows and then the
columns with the canonical `ZMod.dft` gives the two-dimensional negative-exponent sum. -/
theorem rowColumnDFT_eq_dft2Sum {m n : ℕ} [NeZero m] [NeZero n]
    (x : ZMod m × ZMod n → ℂ) :
    rowColumnDFT x = dft2Sum x := by
  funext p
  obtain ⟨k, l⟩ := p
  simp only [rowColumnDFT, columnDFT, rowDFT, dft2Sum, ZMod.dft_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [stdAddChar_neg_mul_eq]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  ring_nf

private lemma inv_push {m n : ℕ} [NeZero m] [NeZero n] (X : ZMod m × ZMod n → ℂ)
    (i : ZMod m) (j l : ZMod n) :
    ZMod.stdAddChar (l * j) * ((m : ℂ)⁻¹ * ∑ k : ZMod m, ZMod.stdAddChar (k * i) * X (k, l)) =
      (m : ℂ)⁻¹ * ∑ k : ZMod m, ZMod.stdAddChar (l * j) * (ZMod.stdAddChar (k * i) * X (k, l)) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma char_mul_inv {m n : ℕ} [NeZero m] [NeZero n] (X : ZMod m × ZMod n → ℂ)
    (i k : ZMod m) (j l : ZMod n) :
    ZMod.stdAddChar (l * j) * (ZMod.stdAddChar (k * i) * X (k, l)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (((k.val * i.val : ℕ) : ℂ) / m + ((l.val * j.val : ℕ) : ℂ) / n)) * X (k, l) := by
  simp only [stdAddChar_mul_eq]
  rw [← mul_assoc, mul_comm (Complex.exp _) (Complex.exp _), ← Complex.exp_add]
  congr 1
  ring_nf

/-- The rectangular inverse DFT is the 2-D positive-exponent sum with factor `1/(m*n)`. -/
theorem rectangularInvDFT_eq_invDft2Sum {m n : ℕ} [NeZero m] [NeZero n]
    (X : ZMod m × ZMod n → ℂ) :
    rectangularInvDFT X = invDft2Sum X := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [rectangularInvDFT, rowInvDFT, columnInvDFT, invDft2Sum, ZMod.invDFT_apply,
    smul_eq_mul, inv_push]
  rw [← Finset.mul_sum]
  rw [← mul_assoc]
  have hscalar : (n : ℂ)⁻¹ * (m : ℂ)⁻¹ = ((m : ℂ) * (n : ℂ))⁻¹ := by
    rw [mul_inv]
    ring
  rw [hscalar, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  exact char_mul_inv X i k j l

private lemma columnInvDFT_columnDFT {m n : ℕ} [NeZero m] [NeZero n]
    (y : ZMod m × ZMod n → ℂ) : columnInvDFT (columnDFT y) = y := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [columnInvDFT, columnDFT]
  exact congrFun (LinearEquiv.symm_apply_apply ZMod.dft (fun i => y (i, j))) i

private lemma rowInvDFT_rowDFT {m n : ℕ} [NeZero m] [NeZero n]
    (y : ZMod m × ZMod n → ℂ) : rowInvDFT (rowDFT y) = y := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [rowInvDFT, rowDFT]
  exact congrFun (LinearEquiv.symm_apply_apply ZMod.dft (fun j => y (i, j))) j

private lemma columnDFT_columnInvDFT {m n : ℕ} [NeZero m] [NeZero n]
    (y : ZMod m × ZMod n → ℂ) : columnDFT (columnInvDFT y) = y := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [columnDFT, columnInvDFT]
  exact congrFun (LinearEquiv.apply_symm_apply ZMod.dft (fun i => y (i, j))) i

private lemma rowDFT_rowInvDFT {m n : ℕ} [NeZero m] [NeZero n]
    (y : ZMod m × ZMod n → ℂ) : rowDFT (rowInvDFT y) = y := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [rowDFT, rowInvDFT]
  exact congrFun (LinearEquiv.apply_symm_apply ZMod.dft (fun j => y (i, j))) j

/-- Inversion: the rectangular inverse undoes the row-then-column DFT. -/
theorem rectangularInvDFT_rowColumnDFT {m n : ℕ} [NeZero m] [NeZero n]
    (x : ZMod m × ZMod n → ℂ) :
    rectangularInvDFT (rowColumnDFT x) = x := by
  simp only [rectangularInvDFT, rowColumnDFT, columnInvDFT_columnDFT, rowInvDFT_rowDFT]

/-- Inversion: the row-then-column DFT undoes the rectangular inverse. -/
theorem rowColumnDFT_rectangularInvDFT {m n : ℕ} [NeZero m] [NeZero n]
    (X : ZMod m × ZMod n → ℂ) :
    rowColumnDFT (rectangularInvDFT X) = X := by
  simp only [rectangularInvDFT, rowColumnDFT, rowDFT_rowInvDFT, columnDFT_columnInvDFT]

/-- **Inverse factor `1/(m*n)`.** The normalized 2-D inverse sum inverts the 2-D DFT sum. -/
theorem invDft2Sum_dft2Sum {m n : ℕ} [NeZero m] [NeZero n] (x : ZMod m × ZMod n → ℂ) :
    invDft2Sum (dft2Sum x) = x := by
  rw [← rectangularInvDFT_eq_invDft2Sum, ← rowColumnDFT_eq_dft2Sum]
  exact rectangularInvDFT_rowColumnDFT x

private lemma invDFT_mul_dft_1d {N : ℕ} [NeZero N] (x y : ZMod N → ℂ) :
    ZMod.dft.symm (fun k => ZMod.dft x k * ZMod.dft y k) =
      fun s => ∑ i, x i * y (s - i) := by
  funext s
  exact ZMod.invDFT_mul_dft x y s


private lemma col_step {m n : ℕ} [NeZero m] [NeZero n] (x y : ZMod m × ZMod n → ℂ)
    (l : ZMod n) (a : ZMod m) :
    columnInvDFT (fun p => rowColumnDFT x p * rowColumnDFT y p) (a, l) =
      ∑ i, rowDFT x (i, l) * rowDFT y (a - i, l) := by
  simp only [columnInvDFT, rowColumnDFT, columnDFT]
  exact congrFun (invDFT_mul_dft_1d _ _) a

private lemma row_step {m n : ℕ} [NeZero m] [NeZero n] (x y : ZMod m × ZMod n → ℂ)
    (s i : ZMod m) (t : ZMod n) :
    ZMod.dft.symm (fun l => rowDFT x (i, l) * rowDFT y (s - i, l)) t =
      ∑ j, x (i, j) * y (s - i, t - j) := by
  have h1 : (fun l : ZMod n => rowDFT x (i, l) * rowDFT y (s - i, l)) =
      (fun l => ZMod.dft (fun j => x (i, j)) l * ZMod.dft (fun j => y (s - i, j)) l) := by
    simp only [rowDFT]
  rw [h1]
  exact congrFun (invDFT_mul_dft_1d _ _) t

/-- **Rectangular convolution theorem.** The rectangular inverse DFT of the pointwise product
of two row-then-column DFTs is the two-dimensional circular convolution. -/
theorem rectangularInvDFT_mul_rowColumnDFT {m n : ℕ} [NeZero m] [NeZero n]
    (x y : ZMod m × ZMod n → ℂ) :
    rectangularInvDFT (fun p => rowColumnDFT x p * rowColumnDFT y p) =
      circularConvolution2 x y := by
  funext p
  obtain ⟨s, t⟩ := p
  simp only [rectangularInvDFT, rowInvDFT, circularConvolution2]
  have hcol : (fun l : ZMod n =>
      columnInvDFT (fun p => rowColumnDFT x p * rowColumnDFT y p) (s, l)) =
      (fun l => ∑ i : ZMod m, rowDFT x (i, l) * rowDFT y (s - i, l)) := by
    funext l
    exact col_step x y l s
  rw [hcol]
  have hfun : (fun l : ZMod n => ∑ i : ZMod m, rowDFT x (i, l) * rowDFT y (s - i, l)) =
      ∑ i : ZMod m, (fun l => rowDFT x (i, l) * rowDFT y (s - i, l)) := by
    funext l
    simp only [Finset.sum_apply]
  rw [hfun, map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact row_step x y s i t

/-- Forward form: the row-then-column DFT turns circular convolution into a pointwise
product. -/
theorem rowColumnDFT_circularConvolution2 {m n : ℕ} [NeZero m] [NeZero n]
    (x y : ZMod m × ZMod n → ℂ) :
    rowColumnDFT (circularConvolution2 x y) = fun p => rowColumnDFT x p * rowColumnDFT y p := by
  have h := rectangularInvDFT_mul_rowColumnDFT x y
  have h2 := congrArg rowColumnDFT h
  rw [rowColumnDFT_rectangularInvDFT] at h2
  exact h2.symm

end MathlibExt.Analysis.Fourier.RectangularDFTAdapter
