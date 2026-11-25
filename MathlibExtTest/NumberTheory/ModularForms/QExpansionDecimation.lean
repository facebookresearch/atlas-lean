/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.QExpansionDecimation

@[expose] public section

universe u

open HahnSeries

/-- Source-shaped consumer: decimation after expansion, with the original
binders. -/
example (K : Type*) [Field K] (p : ℕ) [NeZero p] (x : LaurentSeries K) :
    ModularCurve.qDecimate K p (ModularCurve.qExpand K p x) = x :=
  ModularCurve.qDecimate_qExpand K p x

/-- Coefficient-level consumer over a higher-universe coefficient field. -/
example (K : Type u) [Field K] (p : ℕ) [NeZero p] (x : LaurentSeries K) (k : ℤ) :
    (ModularCurve.qDecimate K p x).coeff k = x.coeff ((p : ℤ) * k) :=
  ModularCurve.coeff_qDecimate K p x k

/-- Boundary: coefficients at indices not divisible by the expansion factor
vanish after expansion, so the factor hypothesis matters. -/
example (R : Type*) [CommRing R] (f : LaurentSeries R) {k : ℤ}
    (hk : ¬ ((2 : ℕ) : ℤ) ∣ k) :
    (ModularCurve.qExpand R 2 f).coeff k = 0 :=
  ModularCurve.qExpand_coeff_of_not_dvd 2 f hk

/-- Expansion by `1` is the identity. -/
example (R : Type*) [CommRing R] (f : LaurentSeries R) :
    ModularCurve.qExpand R 1 f = f :=
  ModularCurve.qExpand_one_apply f

/-- Non-field consumer: decimation undoes expansion over `ℤ`. -/
example (p : ℕ) [NeZero p] (x : LaurentSeries ℤ) :
    ModularCurve.qDecimate ℤ p (ModularCurve.qExpand ℤ p x) = x :=
  ModularCurve.qDecimate_qExpand ℤ p x

/-- Concrete values over `ℤ`: decimation by `2` keeps `5 q ^ 6` as `5 q ^ 3`
and drops the odd-exponent term `7 q ^ 5`. -/
example :
    ModularCurve.qDecimate ℤ 2 (HahnSeries.single 6 (5 : ℤ) + HahnSeries.single 5 7) =
      HahnSeries.single 3 5 := by
  ext k
  simp only [map_add, HahnSeries.coeff_add, ModularCurve.coeff_qDecimate,
    HahnSeries.coeff_single, Nat.cast_ofNat]
  split_ifs <;> omega

/-- Semiring consumer: the coefficient formula over `ℕ`, which is not a ring. -/
example (p : ℕ) [NeZero p] (x : LaurentSeries ℕ) (k : ℤ) :
    (ModularCurve.qDecimate ℕ p x).coeff k = x.coeff ((p : ℤ) * k) :=
  ModularCurve.coeff_qDecimate ℕ p x k

/-- The support bound needs only a zero in the coefficients. -/
example (K : Type*) [Zero K] (x : LaurentSeries K) :
    BddBelow (Function.support fun k : ℤ => x.coeff (((2 : ℕ) : ℤ) * k)) :=
  ModularCurve.bddBelow_support_decimate K 2 x
