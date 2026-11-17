/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod

/-!
# Rectangular two-dimensional DFT adapter

The row-column two-dimensional DFT on `ZMod m × ZMod n` equals
the separable double sum, and its `1/(m · n)`-normalized inverse
exactly inverts it (both directions). Pointwise product in the
transform domain is circular convolution. Impulse validations
and the wrong-exponent and unnormalized-inverse refutations are
included.

Discharges ECE roadmap leaf `ECE.SIG.IMAGEAUDIO.L2` (rectangular
DFT).
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

private lemma conv_summand {N : ℕ} [NeZero N] (x y : ZMod N → ℂ) (s i j k : ZMod N) :
    ZMod.stdAddChar (k * s) * ((ZMod.stdAddChar (-(i * k)) * x i) * (ZMod.stdAddChar (-(j * k)) * y j)) =
      ZMod.stdAddChar (k * (s - i - j)) * (x i * y j) := by
  have hchar : ZMod.stdAddChar (k * s) * ZMod.stdAddChar (-(i * k)) * ZMod.stdAddChar (-(j * k)) =
      ZMod.stdAddChar (k * (s - i - j)) := by
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc ZMod.stdAddChar (k * s) * ((ZMod.stdAddChar (-(i * k)) * x i) * (ZMod.stdAddChar (-(j * k)) * y j))
      = (ZMod.stdAddChar (k * s) * ZMod.stdAddChar (-(i * k)) * ZMod.stdAddChar (-(j * k))) * (x i * y j) := by ring
    _ = ZMod.stdAddChar (k * (s - i - j)) * (x i * y j) := by rw [hchar]

private lemma dist_k {N : ℕ} [NeZero N] (x y : ZMod N → ℂ) (s k : ZMod N) :
    ZMod.stdAddChar (k * s) * ((∑ i, ZMod.stdAddChar (-(i * k)) * x i) * (∑ j, ZMod.stdAddChar (-(j * k)) * y j)) =
      ∑ i, ∑ j, ZMod.stdAddChar (k * (s - i - j)) * (x i * y j) := by
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum, conv_summand]

private lemma hswap_triple {N : ℕ} [NeZero N] (F : ZMod N → ZMod N → ZMod N → ℂ) :
    (∑ k, ∑ i, ∑ j, F k i j) = (∑ i, ∑ j, ∑ k, F k i j) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

private lemma orth {N : ℕ} [NeZero N] (t : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (k * t)) = (if t = 0 then (N : ℂ) else 0) := by
  have h := AddChar.sum_mulShift (R := ZMod N) (R' := ℂ) t (ZMod.isPrimitive_stdAddChar N)
  rw [ZMod.card, Nat.cast_ite, Nat.cast_zero] at h
  exact h

private lemma k_sum {N : ℕ} [NeZero N] (x y : ZMod N → ℂ) (s i j : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (k * (s - i - j)) * (x i * y j)) =
      (if s - i - j = 0 then (N : ℂ) else 0) * (x i * y j) := by
  rw [← Finset.sum_mul, orth]

private lemma j_sum {N : ℕ} [NeZero N] (x y : ZMod N → ℂ) (s i : ZMod N) :
    (∑ j : ZMod N, (if s - i - j = 0 then (N : ℂ) else 0) * (x i * y j)) =
      (N : ℂ) * (x i * y (s - i)) := by
  have hcond : ∀ j : ZMod N, (s - i - j = 0) ↔ (j = s - i) := by
    intro j
    rw [sub_eq_zero]
    exact eq_comm
  simp only [hcond, ite_mul, zero_mul, Fintype.sum_ite_eq']

private lemma invDFT_mul_dft_1d {N : ℕ} [NeZero N] (x y : ZMod N → ℂ) :
    ZMod.dft.symm (fun k => ZMod.dft x k * ZMod.dft y k) =
      fun s => ∑ i, x i * y (s - i) := by
  funext s
  simp only [ZMod.invDFT_apply, ZMod.dft_apply, smul_eq_mul, dist_k, hswap_triple, k_sum, j_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact inv_mul_cancel_left₀ hN _

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

private lemma double_sum_impulse {m n : ℕ} [NeZero m] [NeZero n]
    (F : ZMod m → ZMod n → ℂ) (a : ZMod m) (b : ZMod n) :
    (∑ i : ZMod m, ∑ j : ZMod n, (if (i, j) = (a, b) then F i j else 0)) = F a b := by
  have houter : ∀ i : ZMod m, i ∈ Finset.univ → i ≠ a →
      (∑ j : ZMod n, (if (i, j) = (a, b) then F i j else 0)) = 0 := by
    intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    have hne : (i, j) ≠ (a, b) := by
      intro hcon
      simp only [Prod.mk.injEq] at hcon
      exact hi hcon.1
    simp [hne]
  have hinner : ∀ j : ZMod n, j ∈ Finset.univ → j ≠ b →
      (if (a, j) = (a, b) then F a j else 0) = 0 := by
    intro j _ hj
    have hne : (a, j) ≠ (a, b) := by
      intro hcon
      simp only [Prod.mk.injEq] at hcon
      exact hj hcon.2
    simp [hne]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a) houter,
    Finset.sum_eq_single_of_mem b (Finset.mem_univ b) hinner]
  simp

private lemma dft2Sum_impulse {m n : ℕ} [NeZero m] [NeZero n] (a : ZMod m) (b : ZMod n)
    (k : ZMod m) (l : ZMod n) :
    dft2Sum (fun p : ZMod m × ZMod n => if p = (a, b) then (1 : ℂ) else 0) (k, l) =
      Complex.exp (-2 * Real.pi * Complex.I *
        (((a.val * k.val : ℕ) : ℂ) / m + ((b.val * l.val : ℕ) : ℂ) / n)) := by
  simp only [dft2Sum, mul_ite, mul_one, mul_zero]
  exact double_sum_impulse _ _ _

/-- Validation (`2 × 3`): the impulse at the origin has the all-ones spectrum. -/
theorem rowColumnDFT_impulse_origin :
    rowColumnDFT (fun p : ZMod 2 × ZMod 3 => if p = (0, 0) then (1 : ℂ) else 0) =
      fun _ => 1 := by
  rw [rowColumnDFT_eq_dft2Sum]
  funext p
  obtain ⟨k, l⟩ := p
  rw [dft2Sum_impulse]
  simp

/-- Validation (`2 × 3`, shifted impulse): the impulse at `(1, 1)` has value
`exp (-πi) exp (-2πi/3) = -exp (-2πi/3)` at bin `(1, 1)`. -/
theorem rowColumnDFT_impulse_one_one :
    rowColumnDFT (fun p : ZMod 2 × ZMod 3 => if p = (1, 1) then (1 : ℂ) else 0) (1, 1) =
      -Complex.exp (-(2 * Real.pi * Complex.I / 3)) := by
  rw [rowColumnDFT_eq_dft2Sum, dft2Sum_impulse]
  have h1 : (1 : ZMod 2).val = 1 := by decide
  have h2 : (1 : ZMod 3).val = 1 := by decide
  rw [h1, h2]
  have harg : (-2 * Real.pi * Complex.I *
      ((((1 * 1 : ℕ)) : ℂ) / ((2 : ℕ) : ℂ) + ((((1 * 1 : ℕ)) : ℂ)) / ((3 : ℕ) : ℂ)) : ℂ) =
      (-(Real.pi * Complex.I)) + (-(2 * Real.pi * Complex.I / 3)) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_neg_pi_mul_I]
  ring

/-- Validation (`2 × 3`): the positive-exponent variant of the 2-D sum is not the
row-then-column canonical DFT. -/
theorem rowColumnDFT_ne_positiveExponentSum :
    ¬ ∀ x : ZMod 2 × ZMod 3 → ℂ, rowColumnDFT x = fun p => ∑ i : ZMod 2, ∑ j : ZMod 3,
      Complex.exp (2 * Real.pi * Complex.I *
        (((i.val * p.1.val : ℕ) : ℂ) / 2 + ((j.val * p.2.val : ℕ) : ℂ) / 3)) * x (i, j) := by
  intro hall
  have h1 : (1 : ZMod 3).val = 1 := by decide
  have h := congrFun (hall (fun p : ZMod 2 × ZMod 3 => if p = (0, 1) then (1 : ℂ) else 0)) (0, 1)
  rw [rowColumnDFT_eq_dft2Sum, dft2Sum_impulse] at h
  simp only [mul_ite, mul_one, mul_zero, double_sum_impulse, h1, ZMod.val_zero] at h
  have hBA : ((2 * Real.pi * Complex.I * ((((0 : ℕ)) : ℂ) / 2 + (((1 : ℕ)) : ℂ) / 3)) -
      (-2 * Real.pi * Complex.I * ((((0 : ℕ)) : ℂ) / (((2 : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ) / (((3 : ℕ)) : ℂ))) : ℂ) =
      2 * Real.pi * Complex.I * ((2 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) := by
    push_cast
    ring
  have hsub : Complex.exp ((2 * Real.pi * Complex.I * ((((0 : ℕ)) : ℂ) / 2 + (((1 : ℕ)) : ℂ) / 3)) -
      (-2 * Real.pi * Complex.I * ((((0 : ℕ)) : ℂ) / (((2 : ℕ)) : ℂ) + (((1 : ℕ)) : ℂ) / (((3 : ℕ)) : ℂ)))) = 1 :=
    Complex.exp_eq_exp_iff_exp_sub_eq_one.mp h.symm
  rw [hBA] at hsub
  have hdiv := (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 2) (N := 3) (by decide)).mp hsub
  norm_num at hdiv

private lemma invDft2Sum_impulse {m n : ℕ} [NeZero m] [NeZero n] (a : ZMod m) (b : ZMod n)
    (i : ZMod m) (j : ZMod n) :
    invDft2Sum (fun p : ZMod m × ZMod n => if p = (a, b) then (1 : ℂ) else 0) (i, j) =
      ((m : ℂ) * n)⁻¹ * Complex.exp (2 * Real.pi * Complex.I *
        (((a.val * i.val : ℕ) : ℂ) / m + ((b.val * j.val : ℕ) : ℂ) / n)) := by
  simp only [invDft2Sum, mul_ite, mul_one, mul_zero]
  congr 1
  exact double_sum_impulse _ _ _

/-- Validation (`2 × 3`): the inverse sum without the factor `1/(m*n)` is not the rectangular
inverse DFT. -/
theorem rectangularInvDFT_ne_unnormalizedSum :
    ¬ ∀ X : ZMod 2 × ZMod 3 → ℂ, rectangularInvDFT X = fun p => ∑ k : ZMod 2, ∑ l : ZMod 3,
      Complex.exp (2 * Real.pi * Complex.I *
        (((k.val * p.1.val : ℕ) : ℂ) / 2 + ((l.val * p.2.val : ℕ) : ℂ) / 3)) * X (k, l) := by
  intro hall
  have h := congrFun (hall (fun p : ZMod 2 × ZMod 3 => if p = (0, 0) then (1 : ℂ) else 0)) (0, 0)
  rw [rectangularInvDFT_eq_invDft2Sum, invDft2Sum_impulse] at h
  simp only [mul_ite, mul_one, mul_zero, double_sum_impulse] at h
  simp at h
  norm_num at h

end MathlibExt.Analysis.Fourier.RectangularDFTAdapter
