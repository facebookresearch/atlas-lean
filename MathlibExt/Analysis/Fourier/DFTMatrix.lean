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

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Fintype.BigOperators

/-!
# Normalized finite-dimensional DFT matrix

This module defines the normalized discrete Fourier transform matrix on
`Fin d` with an integer sign parameter.

## Definition

For `d : ℕ` and `s : ℤ`, the DFT matrix is

```
dftMatrix d s (i, j) = exp (2 * π * I * s * i * j / d) / √(d)
```

with `i, j : Fin d` using 0-based indexing (`i.val`, `j.val`).
The factor `1/√d` is the unitary normalization. The case `d = 0`
is defined as `0` because division by zero in a field yields `0`;
unitarity statements require `0 < d`.

## Sign convention

`s = 1` gives the forward transform `exp (+2πI j k / d)` and `s = -1`
gives the backward transform `exp (-2πI j k / d)`. The two are
adjoint of each other: `conj(exp(... s ...)) = exp(... (-s) ...)`.

## Indexing

`Fin d` is 0-based, so indices `j, k ∈ {0, …, d-1}` appear as
`j.val`, `k.val` in the exponent.

## Main definitions

* `dftMatrix d s` – normalized `Fin d × Fin d` complex DFT matrix.
* `dftMatrix_apply` – entry formula.
* `dftUnitaryPos d hd` – bundled `unitaryGroup (Fin d) ℂ` for `s = +1`.
* `dftUnitaryNeg d hd` – bundled `unitaryGroup (Fin d) ℂ` for `s = -1`.

Roots-of-unity, conjugation, transpose, divisibility, geometric-sum,
and matrix unitarity facts used in the proof are kept private.
-/

@[expose] public section

open Complex Matrix Finset
open scoped Matrix ComplexConjugate

namespace Matrix

/-! ### Definition -/

/-- Normalized DFT matrix on `Fin d` with sign `s : ℤ`.
Entry `i, j` is `exp (2 * π * I * s * i * j / d) / √d`. For `d = 0`
the value is `0` (field division by zero), but unitary lemmas require `0 < d`. -/
noncomputable def dftMatrix (d : ℕ) (s : ℤ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    let sqrtD : ℂ := (Real.sqrt (d : ℝ) : ℂ)
    Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
          (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) /
      sqrtD

/-- Entry formula for `dftMatrix`. -/
@[simp]
theorem dftMatrix_apply (d : ℕ) (s : ℤ) (i j : Fin d) :
    dftMatrix d s i j =
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) /
        (Real.sqrt (d : ℝ) : ℂ) :=
  rfl

/-! ### Private auxiliary lemmas about `Real.sqrt` and casts -/

private lemma sqrtD_ne_zero {d : ℕ} (hd : 0 < d) :
    (Real.sqrt (d : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < Real.sqrt (d : ℝ) := by
    rw [Real.sqrt_pos]
    exact Nat.cast_pos.mpr hd
  have hne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hpos
  intro heq
  have : Real.sqrt (d : ℝ) = 0 := by
    have := Complex.ofReal_eq_zero.mp heq
    exact this
  exact hne this

private lemma natCast_ne_zero_ℂ {d : ℕ} (hd : 0 < d) : (d : ℂ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hd)

private lemma sqrtD_mul_self {d : ℕ} :
    (Real.sqrt (d : ℝ) : ℂ) * (Real.sqrt (d : ℝ) : ℂ) = (d : ℂ) := by
  have h : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg d)
  calc
    (Real.sqrt (d : ℝ) : ℂ) * (Real.sqrt (d : ℝ) : ℂ)
        = ((Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul]
    _ = ((d : ℝ) : ℂ) := by rw [h]
    _ = (d : ℂ) := by norm_cast

private lemma inv_sqrtD_mul_inv_sqrtD {d : ℕ} (_hd : 0 < d) :
    (Real.sqrt (d : ℝ) : ℂ)⁻¹ * (Real.sqrt (d : ℝ) : ℂ)⁻¹ =
      (d : ℂ)⁻¹ := by
  calc
    (Real.sqrt (d : ℝ) : ℂ)⁻¹ * (Real.sqrt (d : ℝ) : ℂ)⁻¹
        = ((Real.sqrt (d : ℝ) : ℂ) * (Real.sqrt (d : ℝ) : ℂ))⁻¹ := by
          rw [_root_.mul_inv]
    _ = (d : ℂ)⁻¹ := by rw [sqrtD_mul_self]

private lemma conj_pi : star (Real.pi : ℂ) = (Real.pi : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

private lemma conj_two : star (2 : ℂ) = (2 : ℂ) := by
  have : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
  rw [this, Complex.star_def, Complex.conj_ofReal]

private lemma conj_natCast_ℂ (n : ℕ) : star (n : ℂ) = (n : ℂ) := by
  rw [Complex.star_def]
  exact Complex.conj_natCast n

private lemma conj_intCast_ℂ (z : ℤ) : star (z : ℂ) = (z : ℂ) := by
  rw [Complex.star_def]
  have : (z : ℂ) = ((z : ℝ) : ℂ) := by norm_cast
  rw [this, Complex.conj_ofReal]

private lemma star_I : star Complex.I = -Complex.I := by
  rw [Complex.star_def, Complex.conj_I]

private lemma conj_dftArg (d : ℕ) (s : ℤ) (i j : ℕ) :
    star ((2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
      (i : ℂ) * (j : ℂ) / (d : ℂ)) : ℂ) =
      -(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
        (i : ℂ) * (j : ℂ) / (d : ℂ)) := by
  rw [star_div₀]
  simp only [star_mul]
  rw [conj_two, conj_pi, star_I, conj_intCast_ℂ,
    conj_natCast_ℂ, conj_natCast_ℂ, conj_natCast_ℂ]
  ring

private lemma conj_dftArg_fin (d : ℕ) (s : ℤ) (i j : Fin d) :
    star ((2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
      (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) : ℂ) =
      -(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
        (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) :=
  conj_dftArg d s i.val j.val

private lemma conj_sqrtD (d : ℕ) :
    star (Real.sqrt (d : ℝ) : ℂ) = (Real.sqrt (d : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-! ### Private conjugation and transpose -/

private theorem dftMatrix_conj (d : ℕ) (s : ℤ) (i j : Fin d) :
    star (dftMatrix d s i j) =
      Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (i.val : ℂ) * (j.val : ℂ) / (d : ℂ))) /
        (Real.sqrt (d : ℝ) : ℂ) := by
  unfold dftMatrix
  simp only
  rw [star_div₀, conj_sqrtD]
  rw [Complex.star_def]
  rw [← Complex.exp_conj]
  have h := conj_dftArg_fin d s i j
  rw [Complex.star_def] at h
  calc
    cexp (conj (2 * ↑Real.pi * I * ↑s * ↑↑i * ↑↑j / ↑d)) / ↑√↑d
        = cexp (-(2 * ↑Real.pi * I * ↑s * ↑↑i * ↑↑j / ↑d)) / ↑√↑d := by rw [h]

private theorem dftMatrix_conj_eq_neg (d : ℕ) (s : ℤ) (i j : Fin d) :
    star (dftMatrix d s i j) = dftMatrix d (-s) i j := by
  rw [dftMatrix_conj]
  unfold dftMatrix
  simp only
  have hneg : -(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
      (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((-s : ℤ) : ℂ) *
        (i.val : ℂ) * (j.val : ℂ) / (d : ℂ) := by
    push_cast
    ring
  rw [hneg]

private lemma dftMatrix_symm (d : ℕ) (s : ℤ) (i j : Fin d) :
    dftMatrix d s i j = dftMatrix d s j i := by
  unfold dftMatrix
  simp only
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) * (i.val : ℂ) * (j.val : ℂ) /
        (d : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) * (j.val : ℂ) * (i.val : ℂ) / (d : ℂ) := by
    ring
  rw [harg]

private theorem dftMatrix_conjTranspose_apply (d : ℕ) (s : ℤ) (i j : Fin d) :
    (star (dftMatrix d s)) j i = dftMatrix d (-s) i j := by
  rw [Matrix.star_apply]
  exact dftMatrix_conj_eq_neg d s i j

private theorem dftMatrix_conjTranspose (d : ℕ) (s : ℤ) :
    star (dftMatrix d s) = dftMatrix d (-s) := by
  ext i j
  have h := dftMatrix_conjTranspose_apply d s j i
  rw [h]
  exact dftMatrix_symm d (-s) j i

/-! ### Private roots-of-unity lemmas -/

private lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_ne_zero (mul_ne_zero h2 hpi) hI

private theorem exp_two_pi_int_div_eq_one_iff {d : ℕ} (hd : 0 < d) (t : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ)) = 1 ↔
      (d : ℤ) ∣ t := by
  have hd_ne : (d : ℂ) ≠ 0 := natCast_ne_zero_ℂ hd
  have h2pi_ne := two_pi_I_ne_zero
  constructor
  · intro heq
    rw [Complex.exp_eq_one_iff] at heq
    obtain ⟨n, hn⟩ := heq
    have hmul : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
        n * (2 * (Real.pi : ℂ) * Complex.I) * (d : ℂ) := by
      calc
        2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
            = 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ) * (d : ℂ) := by
              rw [div_mul_cancel₀ _ hd_ne]
        _ = n * (2 * (Real.pi : ℂ) * Complex.I) * (d : ℂ) := by
              rw [hn]
    have h_eq : (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (d : ℂ)) := by
      calc
        (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
            = 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) := by ring
        _ = n * (2 * (Real.pi : ℂ) * Complex.I) * (d : ℂ) := hmul
        _ = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (d : ℂ)) := by ring
    have h_t_eq : (t : ℂ) = (n : ℂ) * (d : ℂ) := by
      exact mul_left_cancel₀ h2pi_ne h_eq
    have hInt : (t : ℂ) = ((n * (d : ℤ) : ℤ) : ℂ) := by
      calc
        (t : ℂ) = (n : ℂ) * (d : ℂ) := h_t_eq
        _ = ((n * (d : ℤ) : ℤ) : ℂ) := by push_cast; ring
    have hinj : Function.Injective (Int.cast : ℤ → ℂ) :=
      fun _ _ h => by exact_mod_cast h
    have ht_eq : t = n * (d : ℤ) := hinj hInt
    exact ⟨n, by rw [ht_eq, mul_comm]⟩
  · intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hk' : (t : ℂ) = (k : ℂ) * (d : ℂ) := by
      have hk_comm : t = k * (d : ℤ) := by rw [hk, mul_comm]
      calc
        (t : ℂ) = ((k * (d : ℤ) : ℤ) : ℂ) := by rw [hk_comm]
        _ = (k : ℂ) * (d : ℂ) := by push_cast; ring
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      calc
        2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ)
            = 2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) * (d : ℂ)) / (d : ℂ) := by
              rw [hk']
        _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
              field_simp
    calc
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ))
          = Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by rw [harg]
      _ = Complex.exp ((k * (2 * (Real.pi : ℂ) * Complex.I) : ℂ)) := by ring_nf
      _ = 1 := by
          have : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
              (k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
          rw [this]
          exact Complex.exp_int_mul_two_pi_mul_I k

private theorem exp_two_pi_int_mul (t : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = 1 := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I t

private theorem exp_div_pow_eq_one {d : ℕ} (hd : 0 < d) (t : ℤ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ))) ^ d = 1 := by
  have hd_ne : (d : ℂ) ≠ 0 := natCast_ne_zero_ℂ hd
  have h_smul : (d : ℕ) • (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) := by
    calc
      (d : ℕ) • (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ))
          = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ)) := by
            rw [nsmul_eq_mul]
      _ = 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) := by
            rw [mul_div_cancel₀ _ hd_ne]
  calc
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ))) ^ d
        = Complex.exp ((d : ℕ) • (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ))) := by
          rw [Complex.exp_nsmul]
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by rw [h_smul]
    _ = 1 := exp_two_pi_int_mul t

private theorem sum_range_exp_two_pi_int_div {d : ℕ} (hd : 0 < d) (t : ℤ) :
    ∑ k ∈ Finset.range d,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k : ℂ) / (d : ℂ)) =
      if (d : ℤ) ∣ t then (d : ℂ) else 0 := by
  let z : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ))
  have hz_pow : z ^ d = 1 := exp_div_pow_eq_one hd t
  have hz_k : ∀ k : ℕ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k : ℂ) / (d : ℂ)) = z ^ k := by
    intro k
    have h_arg : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k : ℂ) / (d : ℂ) =
        k • (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ)) := by
      calc
        2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k : ℂ) / (d : ℂ)
            = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ)) := by ring
        _ = k • (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ)) := by
              rw [nsmul_eq_mul, mul_comm]
    calc
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k : ℂ) / (d : ℂ))
          = Complex.exp (k • (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ))) := by
            rw [h_arg]
      _ = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) / (d : ℂ))) ^ k := by
            rw [Complex.exp_nsmul]
      _ = z ^ k := rfl
  simp_rw [hz_k]
  by_cases h_eq_one : z = 1
  · have hdvd : (d : ℤ) ∣ t := by
      rw [← exp_two_pi_int_div_eq_one_iff hd]
      exact h_eq_one
    rw [ite_eq_left hdvd]
    have h_pow_one : ∀ k : ℕ, z ^ k = 1 := fun k => by rw [h_eq_one, one_pow]
    simp_rw [h_pow_one]
    have h_sum : ∑ _k ∈ Finset.range d, (1 : ℂ) = (d : ℂ) := by
      calc
        ∑ _k ∈ Finset.range d, (1 : ℂ)
            = (Finset.range d).card • (1 : ℂ) := by rw [Finset.sum_const]
        _ = (d : ℕ) • (1 : ℂ) := by rw [Finset.card_range]
        _ = (d : ℂ) := by rw [nsmul_eq_mul, mul_one]
    exact h_sum
  · have h_not_dvd : ¬(d : ℤ) ∣ t := by
      intro hdvd
      have := (exp_two_pi_int_div_eq_one_iff hd t).mpr hdvd
      exact h_eq_one this
    rw [ite_eq_right h_not_dvd]
    have h_ge : ∑ k ∈ Finset.range d, z ^ k =
        (z ^ d - 1) / (z - 1) := by
      rw [geom_sum_eq h_eq_one]
    rw [h_ge, hz_pow, sub_self, zero_div]

private theorem sum_fin_exp_two_pi_int_div {d : ℕ} (hd : 0 < d) (t : ℤ) :
    ∑ k : Fin d,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k.val : ℂ) / (d : ℂ)) =
      if (d : ℤ) ∣ t then (d : ℂ) else 0 := by
  have hrange := sum_range_exp_two_pi_int_div hd t
  calc
    ∑ k : Fin d,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k.val : ℂ) / (d : ℂ))
        = ∑ k ∈ Finset.range d,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k : ℂ) / (d : ℂ)) := by
          rw [← Fin.sum_univ_eq_sum_range (fun k =>
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (k : ℂ) / (d : ℂ)))]
    _ = _ := hrange

/-! ### Private divisibility helpers -/

private lemma fin_sub_dvd_eq {d : ℕ} (hd : 0 < d) {a b : Fin d}
    (hdiv : (d : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ))) : a = b := by
  have ha_lt : (a.val : ℤ) < (d : ℤ) := by exact_mod_cast a.is_lt
  have hb_lt : (b.val : ℤ) < (d : ℤ) := by exact_mod_cast b.is_lt
  have ha_nonneg : 0 ≤ (a.val : ℤ) := by exact_mod_cast Nat.zero_le _
  have hb_nonneg : 0 ≤ (b.val : ℤ) := by exact_mod_cast Nat.zero_le _
  obtain ⟨k, hk⟩ := hdiv
  have hk_eq : (a.val : ℤ) - (b.val : ℤ) = (d : ℤ) * k := hk
  have h_abs_lt : |((a.val : ℤ) - (b.val : ℤ))| < (d : ℤ) := by
    rw [abs_lt]
    constructor
    · have : -(d : ℤ) < (a.val : ℤ) - (b.val : ℤ) := by omega
      exact this
    · have : (a.val : ℤ) - (b.val : ℤ) < (d : ℤ) := by omega
      exact this
  have hk_zero : k = 0 := by
    by_contra hk_ne
    have h_abs_eq : |((a.val : ℤ) - (b.val : ℤ))| = |k| * (d : ℤ) := by
      calc
        |((a.val : ℤ) - (b.val : ℤ))| = |(d : ℤ) * k| := by rw [hk_eq]
        _ = |(d : ℤ)| * |k| := abs_mul _ _
        _ = (d : ℤ) * |k| := by
          rw [abs_of_nonneg (by exact_mod_cast Nat.zero_le d)]
        _ = |k| * (d : ℤ) := by ring
    have hk_abs_pos : 0 < |k| := abs_pos.mpr hk_ne
    have hk_ge_one : 1 ≤ |k| := by omega
    have h_ge : (d : ℤ) ≤ |((a.val : ℤ) - (b.val : ℤ))| := by
      calc
        (d : ℤ) = 1 * (d : ℤ) := by ring
        _ ≤ |k| * (d : ℤ) := by
          exact mul_le_mul_of_nonneg_right hk_ge_one (by omega)
        _ = |((a.val : ℤ) - (b.val : ℤ))| := by rw [← h_abs_eq]
    linarith
  have hab_eq : (a.val : ℤ) = (b.val : ℤ) := by
    have : (a.val : ℤ) - (b.val : ℤ) = 0 := by rw [hk_eq, hk_zero, mul_zero]
    omega
  exact Fin.ext (by exact_mod_cast hab_eq)

private lemma dvd_smul_fin_sub_iff {d : ℕ} (hd : 0 < d) {a b : Fin d}
    {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (d : ℤ) ∣ s * ((a.val : ℤ) - (b.val : ℤ)) ↔ a = b := by
  constructor
  · intro hdiv
    have hdiv' : (d : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ)) := by
      rcases hs with rfl | rfl
      · simpa using hdiv
      · have h_eq : (-1 : ℤ) * ((a.val : ℤ) - (b.val : ℤ)) =
            -((a.val : ℤ) - (b.val : ℤ)) := by
          ring
        rw [h_eq] at hdiv
        exact (Int.dvd_neg.mp hdiv)
    exact fin_sub_dvd_eq hd hdiv'
  · intro heq
    rw [heq]
    simp

/-! ### Private unitary identities -/

private lemma dft_entry_mul_conj {d : ℕ} (hd : 0 < d) (s : ℤ)
    (a b : Fin d) (k : Fin d) :
    dftMatrix d s a k * star (dftMatrix d s b k) =
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            ((a.val : ℤ) - (b.val : ℤ) : ℤ) * (k.val : ℂ) / (d : ℂ)) /
        (d : ℂ) := by
  have hsqrt := inv_sqrtD_mul_inv_sqrtD hd
  have h_base : dftMatrix d s a k * star (dftMatrix d s b k) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
          (a.val : ℂ) * (k.val : ℂ) / (d : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (b.val : ℂ) * (k.val : ℂ) / (d : ℂ))) *
          ((Real.sqrt (d : ℝ) : ℂ)⁻¹ * (Real.sqrt (d : ℝ) : ℂ)⁻¹) := by
    calc
      dftMatrix d s a k * star (dftMatrix d s b k)
          = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (a.val : ℂ) * (k.val : ℂ) / (d : ℂ)) /
            (Real.sqrt (d : ℝ) : ℂ)) *
            (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
              (b.val : ℂ) * (k.val : ℂ) / (d : ℂ))) /
            (Real.sqrt (d : ℝ) : ℂ)) := by
            rw [dftMatrix_apply, dftMatrix_conj]
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (a.val : ℂ) * (k.val : ℂ) / (d : ℂ)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
              (b.val : ℂ) * (k.val : ℂ) / (d : ℂ))) *
            ((Real.sqrt (d : ℝ) : ℂ)⁻¹ * (Real.sqrt (d : ℝ) : ℂ)⁻¹) := by
            rw [div_mul_div_comm]
            ring
  have h_add : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
          (a.val : ℂ) * (k.val : ℂ) / (d : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (b.val : ℂ) * (k.val : ℂ) / (d : ℂ))) *
          ((Real.sqrt (d : ℝ) : ℂ)⁻¹ * (Real.sqrt (d : ℝ) : ℂ)⁻¹) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
          (a.val : ℂ) * (k.val : ℂ) / (d : ℂ) +
          -(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (b.val : ℂ) * (k.val : ℂ) / (d : ℂ))) *
          (d : ℂ)⁻¹ := by
    rw [← Complex.exp_add, hsqrt]
  have hsub : 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
        (a.val : ℂ) * (k.val : ℂ) / (d : ℂ) +
        -(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
          (b.val : ℂ) * (k.val : ℂ) / (d : ℂ)) =
        2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
          ((a.val : ℂ) - (b.val : ℂ)) * (k.val : ℂ) / (d : ℂ) := by ring
  have hcast : (a.val : ℂ) - (b.val : ℂ) =
        (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ) := by push_cast; ring
  calc
    dftMatrix d s a k * star (dftMatrix d s b k)
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (a.val : ℂ) * (k.val : ℂ) / (d : ℂ) +
            -(2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
              (b.val : ℂ) * (k.val : ℂ) / (d : ℂ))) *
            (d : ℂ)⁻¹ := by rw [h_base, h_add]
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            ((a.val : ℂ) - (b.val : ℂ)) * (k.val : ℂ) / (d : ℂ)) *
            (d : ℂ)⁻¹ := by rw [hsub]
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            ((a.val : ℤ) - (b.val : ℤ) : ℤ) * (k.val : ℂ) / (d : ℂ)) *
            (d : ℂ)⁻¹ := by rw [hcast]
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            ((a.val : ℤ) - (b.val : ℤ) : ℤ) * (k.val : ℂ) / (d : ℂ)) /
          (d : ℂ) := by
          rfl

private lemma dft_sum_div (d : ℕ) (f : Fin d → ℂ) :
    (∑ k : Fin d, f k / (d : ℂ)) = (∑ k : Fin d, f k) / (d : ℂ) := by
  calc
    ∑ k : Fin d, f k / (d : ℂ)
        = ∑ k : Fin d, f k * (d : ℂ)⁻¹ := by simp_rw [div_eq_mul_inv]
    _ = ∑ k ∈ Finset.univ, f k * (d : ℂ)⁻¹ := by rfl
    _ = (∑ k ∈ Finset.univ, f k) * (d : ℂ)⁻¹ := by rw [Finset.sum_mul]
    _ = (∑ k : Fin d, f k) * (d : ℂ)⁻¹ := by rfl
    _ = (∑ k : Fin d, f k) / (d : ℂ) := by rw [div_eq_mul_inv]

private lemma sum_dft_mul_star {d : ℕ} (hd : 0 < d) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (a b : Fin d) :
    ∑ k : Fin d, dftMatrix d s a k * star (dftMatrix d s b k) =
      if a = b then 1 else 0 := by
  have hsum := sum_fin_exp_two_pi_int_div hd (s * ((a.val : ℤ) - (b.val : ℤ)))
  calc
    ∑ k : Fin d, dftMatrix d s a k * star (dftMatrix d s b k)
        = ∑ k : Fin d,
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
                ((a.val : ℤ) - (b.val : ℤ) : ℤ) * (k.val : ℂ) / (d : ℂ)) /
            (d : ℂ) := by
          simp_rw [dft_entry_mul_conj hd s a b]
    _ = (∑ k : Fin d,
            Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * ((s * ((a.val : ℤ) - (b.val : ℤ))) : ℤ) *
                (k.val : ℂ) / (d : ℂ))) /
          (d : ℂ) := by
          have h_eq : ∀ k : Fin d,
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
                  ((a.val : ℤ) - (b.val : ℤ) : ℤ) * (k.val : ℂ) / (d : ℂ)) =
              Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I *
                  ((s * ((a.val : ℤ) - (b.val : ℤ)) : ℤ) : ℤ) *
                  (k.val : ℂ) / (d : ℂ)) := by
            intro k
            have h_cast : (s : ℂ) * (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ) =
                ((s * ((a.val : ℤ) - (b.val : ℤ)) : ℤ) : ℂ) := by push_cast; ring
            calc
              Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
                    ((a.val : ℤ) - (b.val : ℤ) : ℤ) * (k.val : ℂ) / (d : ℂ))
                  = Complex.exp
                    (2 * (Real.pi : ℂ) * Complex.I *
                      ((s : ℂ) * (((a.val : ℤ) - (b.val : ℤ) : ℤ) : ℂ)) *
                      (k.val : ℂ) / (d : ℂ)) := by
                    congr 1; ring
              _ = Complex.exp
                    (2 * (Real.pi : ℂ) * Complex.I *
                      ((s * ((a.val : ℤ) - (b.val : ℤ)) : ℤ) : ℤ) *
                      (k.val : ℂ) / (d : ℂ)) := by rw [h_cast]
          simp_rw [h_eq]
          exact dft_sum_div d _
    _ = (if (d : ℤ) ∣ s * ((a.val : ℤ) - (b.val : ℤ)) then (d : ℂ) else 0) / (d : ℂ) := by
          rw [hsum]
    _ = if a = b then 1 else 0 := by
          by_cases hab : a = b
          · rw [ite_eq_left hab]
            have hdvd : (d : ℤ) ∣ s * ((a.val : ℤ) - (b.val : ℤ)) := by
              rw [hab, sub_self, mul_zero]
              exact dvd_zero _
            rw [ite_eq_left hdvd]
            exact div_self (natCast_ne_zero_ℂ hd)
          · rw [ite_eq_right hab]
            have hndvd : ¬(d : ℤ) ∣ s * ((a.val : ℤ) - (b.val : ℤ)) := by
              intro hdiv
              have := (dvd_smul_fin_sub_iff hd hs).mp hdiv
              exact hab this
            rw [ite_eq_right hndvd, zero_div]

private theorem dftMatrix_mul_conjTranspose {d : ℕ} (hd : 0 < d) (s : ℤ)
    (hs : s = 1 ∨ s = -1) :
    dftMatrix d s * star (dftMatrix d s) = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.one_apply]
  have h_star : ∀ j : Fin d,
      star (dftMatrix d s) j b = star (dftMatrix d s b j) := by
    intro j
    rw [Matrix.star_apply]
  simp_rw [h_star]
  have h := sum_dft_mul_star hd s hs a b
  by_cases hab : a = b
  · have : ∑ j : Fin d, dftMatrix d s a j * star (dftMatrix d s b j) = 1 := by
      rw [h, ite_eq_left hab]
    rw [this]
    simp [hab]
  · have : ∑ j : Fin d, dftMatrix d s a j * star (dftMatrix d s b j) = 0 := by
      rw [h, ite_eq_right hab]
    rw [this]
    simp [hab]

/-! ### Bundled unitary matrices for `±1` -/

/-- DFT unitary for sign `+1`. -/
noncomputable def dftUnitaryPos (d : ℕ) (hd : 0 < d) :
    Matrix.unitaryGroup (Fin d) ℂ where
  val := dftMatrix d 1
  property := by
    rw [Matrix.mem_unitaryGroup_iff]
    exact dftMatrix_mul_conjTranspose hd 1 (Or.inl rfl)

/-- DFT unitary for sign `-1`. -/
noncomputable def dftUnitaryNeg (d : ℕ) (hd : 0 < d) :
    Matrix.unitaryGroup (Fin d) ℂ where
  val := dftMatrix d (-1)
  property := by
    rw [Matrix.mem_unitaryGroup_iff]
    exact dftMatrix_mul_conjTranspose hd (-1) (Or.inr rfl)

/-- The positive-sign DFT unitary has the original positive-sign Fourier matrix as its underlying
matrix. -/
@[simp]
theorem dftUnitaryPos_val (d : ℕ) (hd : 0 < d) :
    (dftUnitaryPos d hd : Matrix (Fin d) (Fin d) ℂ) = dftMatrix d 1 :=
  rfl

/-- The negative-sign DFT unitary has the original negative-sign Fourier matrix as its underlying
matrix. -/
@[simp]
theorem dftUnitaryNeg_val (d : ℕ) (hd : 0 < d) :
    (dftUnitaryNeg d hd : Matrix (Fin d) (Fin d) ℂ) = dftMatrix d (-1) :=
  rfl

end Matrix
