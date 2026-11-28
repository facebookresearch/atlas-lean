/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetCatalan

open MetaMathlibExt PowerSeries

private noncomputable def cat : PowerSeries ℚ := mk fun n => (catalan n : ℚ)

private lemma coeff_mul_one (f g : PowerSeries ℚ) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g)]
  simp [Finset.sum_range_succ]

private lemma coeff_mul_two (f g : PowerSeries ℚ) :
    coeff 2 (f * g) = coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g)]
  simp [Finset.sum_range_succ]

private lemma cat_sq_zero : coeff 0 (cat ^ 2) = 1 := by
  simp [coeff_zero_eq_constantCoeff_apply, cat, catalan_zero]

private lemma cat_sq_one : coeff 1 (cat ^ 2) = 2 := by
  norm_num [pow_two, coeff_mul_one, cat, catalan_zero, catalan_one]

private lemma cat_sq_two : coeff 2 (cat ^ 2) = 5 := by
  norm_num [pow_two, coeff_mul_two, cat, catalan_zero, catalan_one, catalan_two]

private noncomputable def oddDet : PowerSeries ℚ :=
  mk fun m => if m % 2 = 0 ∧ 2 ≤ m then
    toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (2 * i - 1) : ℚ)) (m / 2)
    else 0

-- (1): size zero is excluded, even though its degree is even.
example : coeff 0 oddDet = 0 ∧ coeff 0 (X ^ 2 * cat ^ 2 * (rescale (-1 : ℚ) cat) ^ 2) = 0 := by
  simp [coeff_zero_eq_constantCoeff_apply, oddDet]

-- (1): the size-two determinant is C₁² + C₃ = 6, and the odd degree vanishes on both sides.
example : coeff 4 oddDet = 6 ∧ coeff 3 oddDet = 0 := by
  constructor
  · norm_num [oddDet, toeplitzHessenbergDet_two, catalan_one, catalan_three]
  · norm_num [oddDet]

example : coeff 4 (X ^ 2 * cat ^ 2 * (rescale (-1 : ℚ) cat) ^ 2) = 6 := by
  rw [mul_assoc, pow_two X, mul_assoc, show (4 : ℕ) = (2 + 1) + 1 by decide,
    coeff_succ_X_mul, coeff_succ_X_mul, ← (rescale (-1 : ℚ)).map_pow cat 2, coeff_mul_two]
  simp only [coeff_rescale, cat_sq_zero, cat_sq_one, cat_sq_two]
  norm_num

example : coeff 3 (X ^ 2 * cat ^ 2 * (rescale (-1 : ℚ) cat) ^ 2) = 0 := by
  rw [mul_assoc, pow_two X, mul_assoc, show (3 : ℕ) = (1 + 1) + 1 by decide,
    coeff_succ_X_mul, coeff_succ_X_mul, ← (rescale (-1 : ℚ)).map_pow cat 2, coeff_mul_one]
  simp only [coeff_rescale, cat_sq_zero, cat_sq_one]
  norm_num

private noncomputable def consecutiveDet : PowerSeries ℚ :=
  mk fun n => toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ)) n

-- (2): the constant term uses the empty determinant, and degree two gives 9 - 4 - 5 = 0.
example : coeff 0 (consecutiveDet * (2 - cat ^ 2)) = 1 ∧
    coeff 2 (consecutiveDet * (2 - cat ^ 2)) = 0 := by
  have hzero : coeff 0 consecutiveDet = 1 := by
    rw [consecutiveDet, coeff_mk, toeplitzHessenbergDet_eq_sum_compositions]
    have hlen (c : Composition 0) : c.length = 0 := c.length_eq_zero.mpr rfl
    simp [hlen, composition_card]
  have hcoeff (n : ℕ) : coeff n (2 - cat ^ 2) =
      (if n = 0 then 2 else 0) - coeff n (cat ^ 2) := by
    rw [map_sub]
    exact congrArg (· - coeff n (cat ^ 2)) (coeff_C n 2)
  constructor
  · rw [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hzero,
      hcoeff, cat_sq_zero]
    norm_num
  · rw [coeff_mul_two, hzero, hcoeff, hcoeff, hcoeff, cat_sq_zero, cat_sq_one, cat_sq_two]
    norm_num [consecutiveDet, toeplitzHessenbergDet_one, toeplitzHessenbergDet_two,
      catalan_two, catalan_three]

-- (3): the K₋₁ shift starts with zero; n = 1 has an empty sum and n = 2 has a minus sign.
example :
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else (catalan i : ℚ) - catalan (i - 1)) 1 =
        (-1 : ℚ) ^ (1 - 1 : ℕ) * ∑ i ∈ Finset.Icc 1 (1 - 1), (catalan i : ℚ) ∧
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else (catalan i : ℚ) - catalan (i - 1)) 2 =
        (-1 : ℚ) ^ (2 - 1 : ℕ) * ∑ i ∈ Finset.Icc 1 (2 - 1), (catalan i : ℚ) := by
  constructor
  · norm_num [toeplitzHessenbergDet_one, catalan_one, catalan_zero]
  · norm_num [toeplitzHessenbergDet_two, catalan_one, catalan_zero, catalan_two]

-- (4): the K₀ shift gives 1 at n = 1 and −2 at n = 2, including C₀ in both sums.
example :
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else (catalan (i + 1) : ℚ) - catalan i) 1 =
        (-1 : ℚ) ^ (1 - 1 : ℕ) * ∑ i ∈ Finset.range 1, (catalan i : ℚ) ∧
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else (catalan (i + 1) : ℚ) - catalan i) 2 =
        (-1 : ℚ) ^ (2 - 1 : ℕ) * ∑ i ∈ Finset.range 2, (catalan i : ℚ) := by
  constructor
  · norm_num [toeplitzHessenbergDet_one, catalan_zero, catalan_one, catalan_two]
  · norm_num [toeplitzHessenbergDet_two, Finset.sum_range_succ, catalan_zero, catalan_one,
      catalan_two, catalan_three]

private noncomputable def differenceDet : PowerSeries ℚ :=
  mk fun n => if n = 0 then 0 else
    toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ) - catalan i) n

-- (5): the positive-size series has no constant term; degree two gives 4 - 1 = 3.
example : coeff 0 differenceDet = 0 ∧
    coeff 2 (differenceDet * (1 - X * cat ^ 3)) = coeff 2 (X * cat ^ 3) := by
  have hzero : coeff 0 differenceDet = 0 := by simp [differenceDet]
  have h0 : coeff 0 (X * cat ^ 3) = 0 := by simp [coeff_zero_eq_constantCoeff_apply]
  have h1 : coeff 1 (X * cat ^ 3) = 1 := by
    rw [show (1 : ℕ) = 0 + 1 by decide, coeff_succ_X_mul]
    simp [coeff_zero_eq_constantCoeff_apply, cat, catalan_zero]
  have h2 : coeff 2 (X * cat ^ 3) = 3 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, coeff_succ_X_mul, pow_succ, coeff_mul_one,
      cat_sq_zero, cat_sq_one]
    norm_num [cat, catalan_zero, catalan_one]
  refine ⟨hzero, ?_⟩
  rw [coeff_mul_two, hzero]
  norm_num [differenceDet, toeplitzHessenbergDet_one, toeplitzHessenbergDet_two, catalan_one,
    catalan_two, catalan_three, map_sub, coeff_one, h0, h1, h2]

-- Client examples specialize each public conjunct at the boundaries computed above.

example :
    coeff 0 oddDet = coeff 0 (X ^ 2 * cat ^ 2 * (rescale (-1 : ℚ) cat) ^ 2) ∧
    coeff 3 oddDet = coeff 3 (X ^ 2 * cat ^ 2 * (rescale (-1 : ℚ) cat) ^ 2) ∧
    coeff 4 oddDet = coeff 4 (X ^ 2 * cat ^ 2 * (rescale (-1 : ℚ) cat) ^ 2) := by
  have h := toeplitzHessenbergDet_catalan.1
  exact ⟨congrArg (coeff 0) h, congrArg (coeff 3) h, congrArg (coeff 4) h⟩

example : coeff 0 (consecutiveDet * (2 - cat ^ 2)) = 1 ∧
    coeff 2 (consecutiveDet * (2 - cat ^ 2)) = 0 := by
  have h : consecutiveDet * (2 - cat ^ 2) = 1 := toeplitzHessenbergDet_catalan.2.1
  rw [h]
  simp [coeff_one]

example :
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else (catalan i : ℚ) - catalan (i - 1)) 1 = 0 ∧
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else (catalan i : ℚ) - catalan (i - 1)) 2 = -1 := by
  constructor
  · simpa using toeplitzHessenbergDet_catalan.2.2.1 1 (by decide)
  · simpa [catalan_one] using toeplitzHessenbergDet_catalan.2.2.1 2 (by decide)

example :
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else (catalan (i + 1) : ℚ) - catalan i) 1 = 1 ∧
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else (catalan (i + 1) : ℚ) - catalan i) 2 = -2 := by
  constructor
  · simpa [catalan_zero] using toeplitzHessenbergDet_catalan.2.2.2.1 1 (by decide)
  · have h := toeplitzHessenbergDet_catalan.2.2.2.1 2 (by decide)
    norm_num [Finset.sum_range_succ, catalan_zero, catalan_one] at h
    exact h

example :
    coeff 0 (differenceDet * (1 - X * cat ^ 3)) = coeff 0 (X * cat ^ 3) ∧
    coeff 2 (differenceDet * (1 - X * cat ^ 3)) = coeff 2 (X * cat ^ 3) := by
  have h := toeplitzHessenbergDet_catalan.2.2.2.2
  exact ⟨congrArg (coeff 0) h, congrArg (coeff 2) h⟩
