/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import MathlibExt.RingTheory.PowerSeries.SeriesDivisorCalculus

/-!
# Tests for the calculus of series-divisors
-/

open PowerSeries MetaMathlibExt

private theorem geometric_recursion {R : Type*} [CommRing R] (n : ℕ) :
    (n : R) * coeff n (mk (1 : ℕ → R)) =
      ∑ i ∈ Finset.Icc 1 n, (1 : ℕ → R) i * coeff (n - i) (mk (1 : ℕ → R)) := by
  simp [Nat.card_Icc]

-- Invert the geometric series with a divisor sequence that is nonzero even at zero.
example : coeff 1 (1 - X : PowerSeries ℤ) = -1 := by
  have h₀ : coeff 0 (1 - X : PowerSeries ℤ) = 1 := by simp
  simpa only [Nat.cast_one, one_mul, Finset.Icc_self, Finset.sum_singleton, Nat.sub_self,
    Pi.one_apply, h₀, mul_one] using
    (series_divisor_calculus (R := ℤ) _ _ geometric_recursion).1 (1 - X)
      (mk_one_mul_one_sub_eq_one ℤ) 1

-- Replacing `q` by `-q` negates the degree-one contribution.
example : coeff 1 (rescale (-1) (mk (1 : ℕ → ℤ))) = -1 := by
  have h₀ : coeff 0 (rescale (-1) (mk (1 : ℕ → ℤ))) = 1 := by simp [coeff_rescale]
  simpa only [Nat.cast_one, one_mul, Finset.Icc_self, Finset.sum_singleton, Nat.sub_self,
    pow_one, Pi.one_apply, h₀, mul_one] using
    (series_divisor_calculus (R := ℤ) _ _ geometric_recursion).2.1 1

-- In the divisible case the only summand comes from `i = 2`, even with a nonunit scale.
example : (2 : ZMod 4) * coeff 2 (expand 2 (by decide) (mk (1 : ℕ → ZMod 4))) = 2 := by
  have h := (series_divisor_calculus (R := ZMod 4) _ _ geometric_recursion).2.2.1 2 (by decide) 2
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)] at h
  have h₀ : coeff 0 (expand 2 (by decide) (mk (1 : ℕ → ZMod 4))) = 1 := by simp [coeff_expand]
  simpa only [ite_eq_right (by decide : ¬ (2 : ℕ) ∣ 1), ite_eq_left (dvd_refl (2 : ℕ)),
    zero_mul, zero_add, Nat.div_self (by decide : 0 < 2), Nat.sub_self, Pi.one_apply, h₀,
    mul_one, Nat.cast_ofNat] using h

-- At degree three the index `i = 2` is divisible, but its complementary degree is not.
example : (3 : ZMod 4) * coeff 3 (expand 2 (by decide) (mk (1 : ℕ → ZMod 4))) = 0 := by
  have h := (series_divisor_calculus (R := ZMod 4) _ _ geometric_recursion).2.2.1 2 (by decide) 3
  have hI : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [hI, Finset.sum_insert (by decide : 1 ∉ ({2, 3} : Finset ℕ)),
    Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)] at h
  have h₁ : coeff (3 - 2) (expand 2 (by decide) (mk (1 : ℕ → ZMod 4))) = 0 :=
    coeff_expand_of_not_dvd 2 (by decide) _ (by decide)
  simpa only [ite_eq_right (by decide : ¬ (2 : ℕ) ∣ 1), ite_eq_right (by decide : ¬ (2 : ℕ) ∣ 3),
    h₁, mul_zero, zero_mul, zero_add, Nat.cast_ofNat] using h

-- The power clause also applies at exponent zero.
example (n : ℕ) : (n : ℤ) * coeff n (mk (1 : ℕ → ℤ) ^ 0) = 0 := by
  simpa only [Nat.cast_zero, zero_mul, Finset.sum_const_zero] using
    (series_divisor_calculus (R := ℤ) _ _ geometric_recursion).2.2.2 0 n
