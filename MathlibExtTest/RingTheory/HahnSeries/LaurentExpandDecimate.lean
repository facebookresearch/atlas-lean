/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HahnSeries.LaurentExpandDecimate

@[expose] public section

universe u

open HahnSeries

/-- Source-shaped consumer: decimation after expansion, with the original
binders. -/
example (K : Type*) [Field K] (p : ℕ) [NeZero p] (x : LaurentSeries K) :
    LaurentSeries.decimate K p (LaurentSeries.expand K p x) = x :=
  LaurentSeries.decimate_expand p x

/-- Coefficient-level consumer over a higher-universe coefficient field. -/
example (K : Type u) [Field K] (p : ℕ) [NeZero p] (x : LaurentSeries K) (k : ℤ) :
    (LaurentSeries.decimate K p x).coeff k = x.coeff ((p : ℤ) * k) :=
  LaurentSeries.coeff_decimate p x k

/-- Boundary: coefficients at indices not divisible by the expansion factor
vanish after expansion, so the factor hypothesis matters. -/
example (R : Type*) [CommRing R] (f : LaurentSeries R) {k : ℤ}
    (hk : ¬ ((2 : ℕ) : ℤ) ∣ k) :
    (LaurentSeries.expand R 2 f).coeff k = 0 :=
  LaurentSeries.coeff_expand_of_not_dvd 2 f hk

/-- Expansion by `1` is the identity. -/
example (R : Type*) [CommRing R] (f : LaurentSeries R) :
    LaurentSeries.expand R 1 f = f :=
  LaurentSeries.expand_one_apply f

/-- Non-field consumer: decimation undoes expansion over `ℤ`. -/
example (p : ℕ) [NeZero p] (x : LaurentSeries ℤ) :
    LaurentSeries.decimate ℤ p (LaurentSeries.expand ℤ p x) = x :=
  LaurentSeries.decimate_expand p x

/-- Concrete values over `ℤ`: decimation by `2` keeps `5 X ^ 6` as `5 X ^ 3`
and drops the odd-exponent term `7 X ^ 5`. -/
example :
    LaurentSeries.decimate ℤ 2 (HahnSeries.single 6 (5 : ℤ) + HahnSeries.single 5 7) =
      HahnSeries.single 3 5 := by
  ext k
  simp only [map_add, HahnSeries.coeff_add, LaurentSeries.coeff_decimate,
    HahnSeries.coeff_single, Nat.cast_ofNat]
  split_ifs <;> omega

/-- Semiring consumer: the coefficient formula over `ℕ`, which is not a ring. -/
example (p : ℕ) [NeZero p] (x : LaurentSeries ℕ) (k : ℤ) :
    (LaurentSeries.decimate ℕ p x).coeff k = x.coeff ((p : ℤ) * k) :=
  LaurentSeries.coeff_decimate p x k

/-- Semiring consumer: decimation undoes expansion over `ℕ`, which is not a ring. -/
example (p : ℕ) [NeZero p] (x : LaurentSeries ℕ) :
    LaurentSeries.decimate ℕ p (LaurentSeries.expand ℕ p x) = x :=
  LaurentSeries.decimate_expand p x

/-- The support bound needs only a zero in the coefficients. -/
example (K : Type*) [Zero K] (x : LaurentSeries K) :
    BddBelow (Function.support fun k : ℤ => x.coeff (((2 : ℕ) : ℤ) * k)) :=
  LaurentSeries.bddBelow_support_decimate 2 x
