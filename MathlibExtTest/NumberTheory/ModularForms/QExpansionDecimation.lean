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
