/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding

@[expose] public section

set_option autoImplicit false

open CSLibExt.Algorithms.Lean.Fourier.FFT.SupportBoundedPadding
open MathlibExt.Analysis.Fourier.RectangularDFTAdapter

/-- Unit-support linear convolution at index 0 is the product `2 * 3 = 6`. -/
example : linearConvolution 1 1 (fun _ => (2 : ℂ)) (fun _ => (3 : ℂ)) 0 = 6 := by
  norm_num [linearConvolution, extendNat]

/-- Unit-support linear convolution at index 1 vanishes. -/
example : linearConvolution 1 1 (fun _ => (2 : ℂ)) (fun _ => (3 : ℂ)) 1 = 0 := by
  norm_num [linearConvolution, extendNat, Finset.sum_range_succ]

/-- The same signals padded to length 3 have cyclic coefficient `6` at index 0. -/
example : cyclicConvolution 3 (zeroExtend 1 3 (fun _ => (2 : ℂ)))
    (zeroExtend 1 3 (fun _ => (3 : ℂ))) 0 = 6 := by
  norm_num [cyclicConvolution, zeroExtend, extendNat]

/-! ### Nontrivial one-dimensional supports

The signals `(1, 2)` and `(3, 4, 5)` have linear convolution `(3, 10, 13, 10)`,
so the exact padding boundary is `N = 2 + 3 - 1 = 4`. -/

/-- The signal `(1, 2)` of support length two. -/
def padSigA : Fin 2 → ℂ := fun i => (i.val : ℂ) + 1

/-- The signal `(3, 4, 5)` of support length three. -/
def padSigB : Fin 3 → ℂ := fun j => (j.val : ℂ) + 3

/-- The full linear convolution is `(3, 10, 13, 10)` and vanishes at the linear length. -/
example : linearConvolution 2 3 padSigA padSigB 0 = 3 ∧
    linearConvolution 2 3 padSigA padSigB 1 = 10 ∧
    linearConvolution 2 3 padSigA padSigB 2 = 13 ∧
    linearConvolution 2 3 padSigA padSigB 3 = 10 ∧
    linearConvolution 2 3 padSigA padSigB 4 = 0 := by
  norm_num [linearConvolution, extendNat, padSigA, padSigB, Finset.sum_range_succ]

/-- Exact boundary `N = 4`, origin: the wrapped term `2 * y(-1 mod 4)` lands on the
zero padding slot, so the cyclic coefficient is the linear `3`. -/
example : cyclicConvolution 4 (zeroExtend 2 4 padSigA) (zeroExtend 3 4 padSigB) 0 = 3 := by
  have hU : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  simp only [cyclicConvolution, hU]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, Finset.sum_singleton]
  simp only [zeroExtend, show (0 : ZMod 4) - 0 = 0 by decide,
    show (0 : ZMod 4) - 1 = 3 by decide, show (0 : ZMod 4) - 2 = 2 by decide,
    show (0 : ZMod 4) - 3 = 1 by decide, show (0 : ZMod 4).val = 0 by decide,
    show (1 : ZMod 4).val = 1 by decide, show (2 : ZMod 4).val = 2 by decide,
    show (3 : ZMod 4).val = 3 by decide]
  norm_num [extendNat, padSigA, padSigB]

/-- Exact boundary `N = 4`, last linear index `t = M + K - 2 = 3`: the cyclic
coefficient is the linear `10`. -/
example : cyclicConvolution 4 (zeroExtend 2 4 padSigA) (zeroExtend 3 4 padSigB) 3 = 10 := by
  have hU : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  simp only [cyclicConvolution, hU]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, Finset.sum_singleton]
  simp only [zeroExtend, show (3 : ZMod 4) - 0 = 3 by decide,
    show (3 : ZMod 4) - 1 = 2 by decide, show (3 : ZMod 4) - 2 = 1 by decide,
    show (3 : ZMod 4) - 3 = 0 by decide, show (0 : ZMod 4).val = 0 by decide,
    show (1 : ZMod 4).val = 1 by decide, show (2 : ZMod 4).val = 2 by decide,
    show (3 : ZMod 4).val = 3 by decide]
  norm_num [extendNat, padSigA, padSigB]

/-- The headline theorem at the exact boundary `N = 4` and last index `t = 3`. -/
example : cyclicConvolution 4 (zeroExtend 2 4 padSigA) (zeroExtend 3 4 padSigB)
    ((3 : ℕ) : ZMod 4) = 10 := by
  rw [padded_cyclic_eq_linear 2 3 4 (by norm_num) (by norm_num) (by norm_num)
    padSigA padSigB 3 (by norm_num)]
  norm_num [linearConvolution, extendNat, padSigA, padSigB, Finset.sum_range_succ]

/-- The headline theorem with larger padding `N = 7 > M + K - 1`. -/
example : cyclicConvolution 7 (zeroExtend 2 7 padSigA) (zeroExtend 3 7 padSigB)
    ((2 : ℕ) : ZMod 7) = 13 := by
  rw [padded_cyclic_eq_linear 2 3 7 (by norm_num) (by norm_num) (by norm_num)
    padSigA padSigB 2 (by norm_num)]
  norm_num [linearConvolution, extendNat, padSigA, padSigB, Finset.sum_range_succ]

/-- One slot short, `N = 3`: the last linear coefficient `10` wraps onto the origin,
giving `3 + 10 = 13` instead of the linear `3`. -/
example : cyclicConvolution 3 (zeroExtend 2 3 padSigA) (zeroExtend 3 3 padSigB) 0 = 13 := by
  have hU : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  simp only [cyclicConvolution, hU]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, Finset.sum_singleton]
  simp only [zeroExtend, show (0 : ZMod 3) - 0 = 0 by decide,
    show (0 : ZMod 3) - 1 = 2 by decide, show (0 : ZMod 3) - 2 = 1 by decide,
    show (0 : ZMod 3).val = 0 by decide, show (1 : ZMod 3).val = 1 by decide,
    show (2 : ZMod 3).val = 2 by decide]
  norm_num [extendNat, padSigA, padSigB]

/-- The one-short alias theorem instantiates at the same supports. -/
example : ∃ x : Fin 2 → ℂ, ∃ y : Fin 3 → ℂ,
    cyclicConvolution 3 (zeroExtend 2 3 x) (zeroExtend 3 3 y) 0 ≠ linearConvolution 2 3 x y 0 :=
  one_short_padding_aliases 2 3 (by norm_num) (by norm_num)

/-! ### Nonsquare two-dimensional supports

The `2 x 2` array `x(i, j) = i + 2 j + 1` is convolved with the `2 x 1` column
`(5, 6)` (linear support `3 x 2`, padded to `3 x 2`) and with the `1 x 2` row
`(5, 6)` (linear support `2 x 3`, padded to `2 x 3`). Each case is one slot short
on a different axis in the aliasing checks. -/

/-- The `2 x 2` array with entries `1, 2` in column `0` and `3, 4` in column `1`. -/
def padArr : Fin 2 × Fin 2 → ℂ := fun p => (p.1.val : ℂ) + 2 * p.2.val + 1

/-- The `2 x 1` column `(5, 6)`. -/
def padCol : Fin 2 × Fin 1 → ℂ := fun p => (p.1.val : ℂ) + 5

/-- The `1 x 2` row `(5, 6)`. -/
def padRow : Fin 1 × Fin 2 → ℂ := fun p => (p.2.val : ℂ) + 5

/-- Linear convolution with the column: `(0, 1) ↦ 15`, `(1, 1) ↦ 38`, `(2, 1) ↦ 24`,
and zero past the second-axis length. -/
example : linearConvolution2 2 2 2 1 padArr padCol (0, 1) = 15 ∧
    linearConvolution2 2 2 2 1 padArr padCol (1, 1) = 38 ∧
    linearConvolution2 2 2 2 1 padArr padCol (2, 1) = 24 ∧
    linearConvolution2 2 2 2 1 padArr padCol (1, 2) = 0 := by
  norm_num [linearConvolution2, extendNat2, padArr, padCol, Finset.sum_range_succ]

/-- Linear convolution with the row: `(1, 0) ↦ 10`, `(1, 1) ↦ 32`, `(1, 2) ↦ 24`,
and zero past the first-axis length. -/
example : linearConvolution2 2 2 1 2 padArr padRow (1, 0) = 10 ∧
    linearConvolution2 2 2 1 2 padArr padRow (1, 1) = 32 ∧
    linearConvolution2 2 2 1 2 padArr padRow (1, 2) = 24 ∧
    linearConvolution2 2 2 1 2 padArr padRow (2, 1) = 0 := by
  norm_num [linearConvolution2, extendNat2, padArr, padRow, Finset.sum_range_succ]

/-- Exact `3 x 2` padding with the column, at `(0, 1)`: the first-axis wrap lands on
padding, so the cyclic coefficient is the linear `15`. -/
example : circularConvolution2 (zeroExtend2 2 2 3 2 padArr) (zeroExtend2 2 1 3 2 padCol)
    ((0 : ZMod 3), (1 : ZMod 2)) = 15 := by
  have hU1 : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  have hU2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  simp only [circularConvolution2, hU1, hU2]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, Finset.sum_singleton]
  simp only [zeroExtend2, show (0 : ZMod 3) - 0 = 0 by decide,
    show (0 : ZMod 3) - 1 = 2 by decide, show (0 : ZMod 3) - 2 = 1 by decide,
    show (1 : ZMod 2) - 0 = 1 by decide, show (1 : ZMod 2) - 1 = 0 by decide,
    show (0 : ZMod 3).val = 0 by decide, show (1 : ZMod 3).val = 1 by decide,
    show (2 : ZMod 3).val = 2 by decide, show (0 : ZMod 2).val = 0 by decide,
    show (1 : ZMod 2).val = 1 by decide]
  norm_num [extendNat2, padArr, padCol]

/-- The two-dimensional headline theorem on the nonsquare `3 x 2` padding at the
last linear index `(2, 1)`. -/
example : circularConvolution2 (zeroExtend2 2 2 3 2 padArr) (zeroExtend2 2 1 3 2 padCol)
    (((2 : ℕ) : ZMod 3), ((1 : ℕ) : ZMod 2)) = 24 := by
  rw [padded_cyclic_eq_linear_two_dim 2 2 2 1 3 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) padArr padCol 2 1 (by norm_num) (by norm_num)]
  norm_num [linearConvolution2, extendNat2, padArr, padCol, Finset.sum_range_succ]

/-- The two-dimensional headline theorem on the nonsquare `2 x 3` padding with the
row at `(1, 1)`. -/
example : circularConvolution2 (zeroExtend2 2 2 2 3 padArr) (zeroExtend2 1 2 2 3 padRow)
    (((1 : ℕ) : ZMod 2), ((1 : ℕ) : ZMod 3)) = 32 := by
  rw [padded_cyclic_eq_linear_two_dim 2 2 1 2 2 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) padArr padRow 1 1 (by norm_num) (by norm_num)]
  norm_num [linearConvolution2, extendNat2, padArr, padRow, Finset.sum_range_succ]

/-- One slot short on the first axis (`2 x 2` padding with the column), at `(0, 1)`:
the coefficient `24` at `(2, 1)` wraps onto `(0, 1)`, giving `15 + 24 = 39`. -/
example : circularConvolution2 (zeroExtend2 2 2 2 2 padArr) (zeroExtend2 2 1 2 2 padCol)
    ((0 : ZMod 2), (1 : ZMod 2)) = 39 := by
  have hU : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  simp only [circularConvolution2, hU]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_singleton,
    Finset.sum_singleton]
  simp only [zeroExtend2, show (0 : ZMod 2) - 0 = 0 by decide,
    show (0 : ZMod 2) - 1 = 1 by decide, show (1 : ZMod 2) - 0 = 1 by decide,
    show (1 : ZMod 2) - 1 = 0 by decide, show (0 : ZMod 2).val = 0 by decide,
    show (1 : ZMod 2).val = 1 by decide]
  norm_num [extendNat2, padArr, padCol]

/-- One slot short on the second axis (`2 x 2` padding with the row), at `(1, 0)`:
the coefficient `24` at `(1, 2)` wraps onto `(1, 0)`, giving `10 + 24 = 34`. -/
example : circularConvolution2 (zeroExtend2 2 2 2 2 padArr) (zeroExtend2 1 2 2 2 padRow)
    ((1 : ZMod 2), (0 : ZMod 2)) = 34 := by
  have hU : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  simp only [circularConvolution2, hU]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_singleton,
    Finset.sum_singleton]
  simp only [zeroExtend2, show (0 : ZMod 2) - 0 = 0 by decide,
    show (0 : ZMod 2) - 1 = 1 by decide, show (1 : ZMod 2) - 0 = 1 by decide,
    show (1 : ZMod 2) - 1 = 0 by decide, show (0 : ZMod 2).val = 0 by decide,
    show (1 : ZMod 2).val = 1 by decide]
  norm_num [extendNat2, padArr, padRow]

/-! ### Bounded zero extension

With the cyclic length covering the support, zero extension keeps every source
entry; with a shorter cyclic length it keeps only the leading entries. -/

/-- Padding `(1, 2)` to length four keeps the entry `2` at index one. -/
example : zeroExtend 2 4 padSigA (((1 : Fin 2).val : ℕ) : ZMod 4) = 2 :=
  (zeroExtend_natCast 2 4 (by norm_num) padSigA 1).trans (by norm_num [padSigA])

/-- Padding to the exact boundary length is injective on length-two signals. -/
example : Function.Injective (zeroExtend 2 4) :=
  zeroExtend_injective 2 4 (by norm_num)

/-- A cyclic length shorter than the support drops trailing entries: on `ZMod 1`
the signals `(0, 1)` and `(0, 0)` have the same image. -/
example : zeroExtend 2 1 (fun i => if i.val = 1 then (1 : ℂ) else 0) =
    zeroExtend 2 1 (fun _ => (0 : ℂ)) := by
  funext i
  rw [Subsingleton.elim i 0]
  simp [zeroExtend, extendNat]

/-- Nonsquare `3 x 2` padding of the `2 x 2` array keeps the entry `4` at `(1, 1)`. -/
example : zeroExtend2 2 2 3 2 padArr
    ((((1 : Fin 2).val : ℕ) : ZMod 3), (((1 : Fin 2).val : ℕ) : ZMod 2)) = 4 :=
  (zeroExtend2_natCast 2 2 3 2 (by norm_num) (by norm_num) padArr 1 1).trans
    (by norm_num [padArr])

/-- Nonsquare `3 x 2` padding is injective on `2 x 1` arrays. -/
example : Function.Injective (zeroExtend2 2 1 3 2) :=
  zeroExtend2_injective 2 1 3 2 (by norm_num) (by norm_num)

/-- For a nonzero cyclic length the coverage bound is also necessary: zero extension
of length-two signals to `ZMod 1` is not injective. -/
example : ¬ Function.Injective (zeroExtend 2 1) := by
  rw [zeroExtend_injective_iff]
  norm_num

/-- Nonzero `2 x 2` padding is not injective on `2 x 3` arrays: the second axis is
one slot short. -/
example : ¬ Function.Injective (zeroExtend2 2 3 2 2) := by
  rw [zeroExtend2_injective_iff 2 3 2 2 (by norm_num) (by norm_num)]
  norm_num

/-- An empty support is injective under any padding, which is why the
two-dimensional characterization assumes nonempty supports. -/
example : Function.Injective (zeroExtend2 2 0 1 1) :=
  fun _ _ _ => funext fun p => p.2.elim0

/-! ### Cyclic length zero

`ZMod 0` is `ℤ` and `ZMod.val` is the absolute value there, so zero extension to
length zero reads every source entry back at its natural index. -/

/-- At length zero the origin reads the first source entry. -/
example (x : Fin 1 → ℂ) : zeroExtend 1 0 x (0 : ZMod 0) = x 0 := by
  simp [zeroExtend, extendNat]

/-- Zero extension of length-two signals to `ZMod 0` is injective although `2 ≤ 0`
fails. -/
example : Function.Injective (zeroExtend 2 0) := by
  intro x x' h
  funext i
  have hi := congrFun h ((i.val : ℕ) : ZMod 0)
  simpa [zeroExtend, extendNat, ZMod.val_natCast, Fin.is_le i] using hi

/-- A zero length on the first axis reads that axis back in full: `2 x 2` arrays
extended to `ZMod 0 x ZMod 2` are distinguished. -/
example : Function.Injective (zeroExtend2 2 2 0 2) := by
  intro x x' h
  funext p
  have hp := congrFun h (((p.1.val : ℕ) : ZMod 0), ((p.2.val : ℕ) : ZMod 2))
  simpa [zeroExtend2, extendNat2, ZMod.val_natCast, Nat.mod_eq_of_lt p.2.isLt, Fin.is_le p.1,
    Fin.is_le p.2] using hp
