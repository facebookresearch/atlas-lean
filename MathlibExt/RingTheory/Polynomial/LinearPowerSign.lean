/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow.lean`
and
`P2M/Sol/S_Polynomial_eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open Polynomial

namespace Polynomial

/-- If a rational polynomial becomes, over `ℚ_[ℓ]`, a sign times a power of a
linear factor `X + C r`, and both its leading sign `a` and its constant
coefficient are `±1`, then the shift `r` itself is `±1` (viewed in `ℚ_[ℓ]`).

Comparing the coefficients of `X ^ (g - 1)` and `X ^ 0` shows `r` comes from
the rational `a * P.coeff (g - 1) / g`, whose `g`-th power is `±1`. -/
public theorem eq_one_or_eq_neg_one_of_map_eq_C_mul_X_add_C_pow
    (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ) (hg : 1 ≤ g) (P : ℚ[X]) (a : ℚ)
    (ha : a = 1 ∨ a = -1)
    (h0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1) (r : ℚ_[ℓ])
    (hP : P.map (algebraMap ℚ ℚ_[ℓ]) =
      C (algebraMap ℚ ℚ_[ℓ] a) * (X + C r) ^ g) :
    r = 1 ∨ r = -1 := by
  set φ : ℚ →+* ℚ_[ℓ] := algebraMap ℚ ℚ_[ℓ] with hφ_def
  have hφ : Function.Injective φ := φ.injective
  have haa : a * a = 1 := by rcases ha with h | h <;> simp [h]
  have hφaa : φ a * φ a = 1 := by rw [← map_mul, haa, map_one]
  have hg0 : (g : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc1 : φ (P.coeff (g - 1)) = φ a * (r * (g : ℚ_[ℓ])) := by
    have h := congrArg (fun p : ℚ_[ℓ][X] => p.coeff (g - 1)) hP
    simp only [coeff_map, coeff_C_mul, coeff_X_add_C_pow, Nat.sub_sub_self hg,
      pow_one, Nat.choose_symm hg, Nat.choose_one_right] at h
    exact h
  have hc0 : φ (P.coeff 0) = φ a * r ^ g := by
    have h := congrArg (fun p : ℚ_[ℓ][X] => p.coeff 0) hP
    simp only [coeff_map, coeff_C_mul, coeff_X_add_C_pow, Nat.sub_zero,
      Nat.choose_zero_right, Nat.cast_one, mul_one] at h
    exact h
  set ρ : ℚ := a * P.coeff (g - 1) / g with hρ_def
  have hr : r = φ ρ := by
    rw [hρ_def, map_div₀, map_mul, hc1, map_natCast]
    field_simp
    have ha2 : φ a ^ 2 = 1 := by rw [pow_two]; exact hφaa
    rw [ha2, mul_one]
  have hρg : ρ ^ g = a * P.coeff 0 := by
    apply hφ
    rw [map_pow, ← hr, map_mul, hc0, ← mul_assoc, hφaa, one_mul]
  have he : a * P.coeff 0 = 1 ∨ a * P.coeff 0 = -1 := by
    rcases ha with h | h <;> rcases h0 with h' | h' <;> simp [h, h']
  have habs : |ρ| = 1 := by
    have h1 : |ρ| ^ g = 1 := by
      rw [← abs_pow, hρg]; rcases he with h | h <;> simp [h]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg ρ) (by omega)).mp h1
  rcases (abs_eq zero_le_one).mp habs with h | h
  · left; rw [hr, h, map_one]
  · right; rw [hr, h, map_neg, map_one]

end Polynomial
