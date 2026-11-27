/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.ShiftLowCoeffDvd

@[expose] public section

open IsLocalRing PowerSeries

-- Consumer with the original binders.
example {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    {n : ℕ} (hn : IsUnit (n : A)) {d e : A} (hd : d ∈ maximalIdeal A) (he : e ≠ 0)
    {u F : A⟦X⟧} (hF : e • F = u * (X + C d) ^ n - X ^ n) {j : ℕ} (hj : j + 2 ≤ n) :
    d ∣ coeff j F :=
  PowerSeries.dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow hn hd he hF hj

-- Higher-universe consumer.
example {A : Type 1} [CommRing A] [IsLocalRing A] [IsDomain A]
    {n : ℕ} (hn : IsUnit (n : A)) {d e : A} (hd : d ∈ maximalIdeal A) (he : e ≠ 0)
    {u F : A⟦X⟧} (hF : e • F = u * (X + C d) ^ n - X ^ n) {j : ℕ} (hj : j + 2 ≤ n) :
    d ∣ coeff j F :=
  PowerSeries.dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow hn hd he hF hj
