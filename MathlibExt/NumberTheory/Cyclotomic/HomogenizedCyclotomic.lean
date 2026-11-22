/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Homogenized cyclotomic values

`homogenizedCyclotomic n a b = ∑ᵢ cᵢ aⁱ b^(φ(n) - i)` for the integer coefficients `cᵢ` of the
`n`-th cyclotomic polynomial, i.e. `b ^ φ(n) Φ_n(a / b)` when `b ≠ 0`. It is the integer
`Φ_n(a, b)` in the factorization `aⁿ - bⁿ = ∏_{d ∣ n} Φ_d(a, b)` used by Zsigmondy-type
arguments (`MathlibExt.NumberTheory.BangZsigmondy`).

## Main definitions

* `MetaMathlibExt.homogenizedCyclotomic`
-/

@[expose] public section

namespace MetaMathlibExt

open Polynomial

/-- The homogenized cyclotomic value `Φ_n(a, b) = ∑ᵢ cᵢ aⁱ b^(φ(n) - i)`, where `cᵢ` are the
integer coefficients of the `n`-th cyclotomic polynomial; equal to `b ^ φ(n) Φ_n(a / b)` when
`b ≠ 0`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 2
(notation `Φ_n(a, b)`, Lemma 3 and the explicit values in the proof of Theorem 1). -/
public noncomputable def homogenizedCyclotomic (n : ℕ) (a b : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (Nat.totient n + 1),
    (cyclotomic n ℤ).coeff i * a ^ i * b ^ (Nat.totient n - i)

/-- `Φ_1(a, b) = a - b`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (v)
(the case `n = 1`). -/
public theorem homogenizedCyclotomic_one (a b : ℤ) : homogenizedCyclotomic 1 a b = a - b := by
  simp [homogenizedCyclotomic, cyclotomic_one, Finset.sum_range_succ, coeff_X, coeff_one]
  ring

/-- `Φ_2(a, b) = a + b`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (v)
(the case `n = 2`). -/
public theorem homogenizedCyclotomic_two (a b : ℤ) : homogenizedCyclotomic 2 a b = a + b := by
  simp [homogenizedCyclotomic, cyclotomic_two, Finset.sum_range_succ, coeff_X, coeff_one]
  ring

/-- `Φ_n(a, 1)` is the cyclotomic polynomial evaluated at `a`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 2
(notation `Φ_n(a, b)`). -/
public theorem homogenizedCyclotomic_one_right (n : ℕ) (a : ℤ) :
    homogenizedCyclotomic n a 1 = (cyclotomic n ℤ).eval a := by
  rw [homogenizedCyclotomic, eval_eq_sum_range, natDegree_cyclotomic]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one]

/-- For `b ≠ 0` in a field, `Φ_n(a, b) = b ^ φ(n) Φ_n(a / b)`.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Section 2
(notation `Φ_n(a, b)`). -/
public theorem homogenizedCyclotomic_cast {K : Type*} [Field K] (n : ℕ) (a b : ℤ)
    (hb : (b : K) ≠ 0) :
    ((homogenizedCyclotomic n a b : ℤ) : K) =
      (b : K) ^ Nat.totient n * (cyclotomic n K).eval ((a : K) / (b : K)) := by
  rw [homogenizedCyclotomic, Int.cast_sum, eval_eq_sum_range, natDegree_cyclotomic,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hle : i ≤ Nat.totient n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcoeff : (cyclotomic n K).coeff i = (((cyclotomic n ℤ).coeff i : ℤ) : K) := by
    rw [← map_cyclotomic n (Int.castRingHom K), coeff_map]
    rfl
  rw [hcoeff, div_pow]
  push_cast
  rw [pow_sub₀ _ hb hle, div_eq_mul_inv]
  ring

end MetaMathlibExt
