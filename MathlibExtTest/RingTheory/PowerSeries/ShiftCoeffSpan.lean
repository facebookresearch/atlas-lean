/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.ShiftCoeffSpan

@[expose] public section

open PowerSeries

-- Consumer with the original binders.
example {A : Type*} [CommRing A] [IsLocalRing A] (n : ℕ) (hn : IsUnit (n : A))
    (u : PowerSeries A) (hu : IsUnit (constantCoeff u))
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (π : A)
    (h : ∀ k < n, coeff k (u * (X - C a) ^ n - X ^ n) ∈ Ideal.span {π}) :
    a ∈ Ideal.span {π} ∧
      ∀ k, k + 2 ≤ n → coeff k (u * (X - C a) ^ n - X ^ n) ∈ Ideal.span {π * a} :=
  PowerSeries.mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span n hn u hu a ha π h

-- Higher-universe consumer.
example {A : Type 1} [CommRing A] [IsLocalRing A] (n : ℕ) (hn : IsUnit (n : A))
    (u : PowerSeries A) (hu : IsUnit (constantCoeff u))
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (π : A)
    (h : ∀ k < n, coeff k (u * (X - C a) ^ n - X ^ n) ∈ Ideal.span {π}) :
    a ∈ Ideal.span {π} ∧
      ∀ k, k + 2 ≤ n → coeff k (u * (X - C a) ^ n - X ^ n) ∈ Ideal.span {π * a} :=
  PowerSeries.mem_span_of_coeff_mul_X_sub_C_pow_sub_X_pow_mem_span n hn u hu a ha π h

-- The stronger arbitrary-ideal helper, with its original binders.
example {A : Type*} [CommRing A] [IsLocalRing A] (u : PowerSeries A)
    (hu : IsUnit (constantCoeff u))
    {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) {n : ℕ} (hn : 1 ≤ n) (hnu : IsUnit (n : A))
    (I : Ideal A) (h : coeff (n - 1) (u * ((X : PowerSeries A) - C a) ^ n - X ^ n) ∈ I) :
    a ∈ I :=
  PowerSeries.mem_of_coeff_pred_mem u hu ha hn hnu I h
