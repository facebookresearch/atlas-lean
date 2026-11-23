/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
generalize the coefficient ring, expose the diagonal series through its coefficients, and bundle
the formal variable difference and its infinite-series inverse as a unit.
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Data.Int.Interval

/-! # Diagonal Laurent-coefficient Hahn series

A coefficient sequence indexed above an arbitrary integer cutoff determines a Hahn series whose
inner and outer exponents lie on one diagonal. Over a commutative ring, this construction gives
the formal inverse of the difference of the two variables and an exact formula for its powers.

Adapted from `eth/proof/rates/GeneralPieces/Series/Rings.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace HahnSeries

open LaurentPolynomial

/-- The Hahn series with coefficient `c y` at inner exponent `d - y` and outer exponent `y`
for every `y ≥ j₀`. -/
noncomputable def diagonalLaurentSeries {R : Type*} [CommSemiring R]
    (d : ℤ) (c : ℤ → R) (j₀ : ℤ) : HahnSeries ℤ (LaurentPolynomial R) :=
  ofSuppBddBelow
    (fun j => if j₀ ≤ j then AddMonoidAlgebra.single (d - j) (c j) else 0)
    ⟨j₀, fun j hj => by
      by_contra h
      simp [h] at hj⟩

/-- The outer coefficient of a diagonal Laurent series. -/
@[simp] theorem coeff_diagonalLaurentSeries {R : Type*} [CommSemiring R]
    (d : ℤ) (c : ℤ → R) (j₀ y : ℤ) :
    (diagonalLaurentSeries d c j₀).coeff y =
      if j₀ ≤ y then AddMonoidAlgebra.single (d - y) (c y) else 0 := by
  rfl

/-- Both coefficients of a diagonal Laurent series, exposing its cutoff and diagonal equation. -/
theorem coeff_coeff_diagonalLaurentSeries {R : Type*} [CommSemiring R]
    (d : ℤ) (c : ℤ → R) (j₀ x y : ℤ) :
    ((diagonalLaurentSeries d c j₀).coeff y).coeff x =
      if j₀ ≤ y ∧ x + y = d then c y else 0 := by
  rw [coeff_diagonalLaurentSeries]
  have hdiag : d - y = x ↔ x + y = d := by omega
  by_cases h : j₀ ≤ y
  · simp only [h, ↓reduceIte]
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    simp [hdiag]
  · simp [h]

/-- Multiplication by the difference of the two variables takes a difference of adjacent
diagonal coefficients. -/
theorem coeff_coeff_variableDifference_mul {R : Type*} [CommRing R]
    (f : HahnSeries ℤ (LaurentPolynomial R)) (x y : ℤ) :
    (((single 0 (T 1) - single 1 1) * f).coeff y).coeff x =
      (f.coeff y).coeff (x - 1) - (f.coeff (y - 1)).coeff x := by
  rw [sub_mul, coeff_sub, coeff_single_mul, coeff_single_mul]
  simp only [sub_zero, T, one_mul]
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (x - 1)
    (fun m _ => by constructor <;> intro hm <;> omega), one_mul]

/-- The formal difference of the inner and outer variables, bundled with its diagonal-series
inverse. -/
noncomputable def variableDifferenceUnit {R : Type*} [CommRing R] :
    (HahnSeries ℤ (LaurentPolynomial R))ˣ := by
  let v : HahnSeries ℤ (LaurentPolynomial R) := single 0 (T 1) - single 1 1
  let e : HahnSeries ℤ (LaurentPolynomial R) :=
    diagonalLaurentSeries (-1) (fun _ => 1) 0
  have h : v * e = 1 := by
    have coeff_laurent_one (z : ℤ) :
        (1 : LaurentPolynomial R).coeff z = if z = 0 then 1 else 0 := by
      rw [← T_zero]
      unfold T
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      simp [eq_comm]
    ext y x
    change (((single 0 (T 1) - single 1 1) * e).coeff y).coeff x =
      ((1 : HahnSeries ℤ (LaurentPolynomial R)).coeff y).coeff x
    rw [coeff_coeff_variableDifference_mul]
    simp only [e, coeff_coeff_diagonalLaurentSeries, coeff_one]
    split_ifs <;> simp_all <;> omega
  exact
    { val := v
      inv := e
      val_inv := h
      inv_val := by simpa only [mul_comm] using h }

/-- The value of `variableDifferenceUnit` is the difference of the two formal variables. -/
@[simp] theorem coe_variableDifferenceUnit {R : Type*} [CommRing R] :
    (variableDifferenceUnit (R := R) : HahnSeries ℤ (LaurentPolynomial R)) =
      single 0 (T 1) - single 1 1 := by
  rfl

/-- The inverse of the formal variable difference is its infinite diagonal Laurent series. -/
@[simp] theorem coe_inv_variableDifferenceUnit {R : Type*} [CommRing R] :
    (↑((variableDifferenceUnit (R := R))⁻¹) : HahnSeries ℤ (LaurentPolynomial R)) =
      diagonalLaurentSeries (-1) (fun _ => 1) 0 := by
  rfl

/-- The `(N + 1)`-st power of the inverse variable difference has negative-binomial
coefficients on one diagonal. -/
theorem coe_inv_variableDifferenceUnit_pow_succ {R : Type*} [CommRing R] (N : ℕ) :
    (↑((variableDifferenceUnit (R := R))⁻¹) : HahnSeries ℤ (LaurentPolynomial R)) ^
        (N + 1) =
      diagonalLaurentSeries (-(N : ℤ) - 1)
        (fun j => ((j.toNat + N).choose N : R)) 0 := by
  induction N with
  | zero =>
      rw [zero_add, pow_one, coe_inv_variableDifferenceUnit]
      ext y x
      rw [coeff_coeff_diagonalLaurentSeries, coeff_coeff_diagonalLaurentSeries]
      simp
  | succ N ih =>
      have key :
          (single 0 (T 1) - single 1 1) *
              diagonalLaurentSeries (-((N + 1 : ℕ) : ℤ) - 1)
                (fun j => ((j.toNat + (N + 1)).choose (N + 1) : R)) 0 =
            (↑((variableDifferenceUnit (R := R))⁻¹) :
              HahnSeries ℤ (LaurentPolynomial R)) ^ (N + 1) := by
        rw [ih]
        ext y x
        rw [coeff_coeff_variableDifference_mul, coeff_coeff_diagonalLaurentSeries,
          coeff_coeff_diagonalLaurentSeries, coeff_coeff_diagonalLaurentSeries]
        by_cases hd : x + y = -(N : ℤ) - 1
        · rcases lt_trichotomy y 0 with hy | hy | hy
          · rw [ite_eq_right (by omega), ite_eq_right (by omega),
              ite_eq_right (by omega), sub_zero]
          · subst hy
            rw [ite_eq_left ⟨le_refl _, by push_cast; omega⟩, ite_eq_right (by omega),
              ite_eq_left ⟨le_refl _, hd⟩]
            simp
          · obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = n + 1 := ⟨(y - 1).toNat, by omega⟩
            rw [ite_eq_left ⟨by omega, by push_cast; omega⟩,
              ite_eq_left ⟨by omega, by push_cast; omega⟩,
              ite_eq_left ⟨by omega, hd⟩]
            have e1 : ((n : ℤ) + 1).toNat = n + 1 := by omega
            have e2 : ((n : ℤ) + 1 - 1).toNat = n := by omega
            rw [e1, e2,
              show n + 1 + (N + 1) = (n + 1 + N) + 1 by ring,
              Nat.choose_succ_succ, show n + 1 + N = n + (N + 1) by ring]
            push_cast
            ring
        · rw [ite_eq_right (fun g => hd (by have := g.2; push_cast at this; omega)),
            ite_eq_right (fun g => hd (by have := g.2; push_cast at this; omega)),
            ite_eq_right (fun g => hd g.2), sub_zero]
      calc
        (↑((variableDifferenceUnit (R := R))⁻¹) :
              HahnSeries ℤ (LaurentPolynomial R)) ^ (N + 1 + 1) =
            (↑((variableDifferenceUnit (R := R))⁻¹) :
                HahnSeries ℤ (LaurentPolynomial R)) ^ (N + 1) *
              ↑((variableDifferenceUnit (R := R))⁻¹) := pow_succ _ _
        _ = ((single 0 (T 1) - single 1 1) *
              ↑((variableDifferenceUnit (R := R))⁻¹)) *
            diagonalLaurentSeries (-((N + 1 : ℕ) : ℤ) - 1)
              (fun j => ((j.toNat + (N + 1)).choose (N + 1) : R)) 0 := by
                rw [← key]
                ring
        _ = _ := by
          rw [← coe_variableDifferenceUnit]
          have hunit :
              (↑(variableDifferenceUnit (R := R)) :
                  HahnSeries ℤ (LaurentPolynomial R)) *
                ↑((variableDifferenceUnit (R := R))⁻¹) = 1 := by
            exact (variableDifferenceUnit (R := R)).val_inv
          rw [hunit, one_mul]

end HahnSeries
