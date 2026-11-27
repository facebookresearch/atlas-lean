/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Convolutions of the series-divisor of an invertible power series

The recurrence for the series-divisor gives the identity `X * derivative A = S * A`,
where `S` is the series with coefficients `s`. The product rule applied to `A * B = 1`
then gives the corresponding identity for `B`.
-/

open PowerSeries

namespace MetaMathlibExt

/-- **Convolution identities for the series-divisor of an invertible series.** Let $R$ be a
commutative ring and let $A$, $B$ be formal power series over $R$ with coefficients $a(k)$,
$b(k)$ and $AB = 1$. Let $s : \mathbb{N} \to R$ satisfy $s(0) = 0$ and
$k\,a(k) = \sum_{i=1}^{k} s(i)\,a(k-i)$ for every $k \ge 0$ (that is, $s$ is a series-divisor
of $A$). Then for every $n \ge 0$,
$$s(n) = \sum_{i=0}^{n} (n-i)\,a(n-i)\,b(i)$$
and
$$\sum_{i=1}^{n} s(n-i)\,s(i) = -\sum_{i=1}^{n} i\,(n-i)\,a(n-i)\,b(i).$$

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 25
(`jis-2024-24.1.6-lem-25`). -/
public theorem series_divisor_inverse_convolution {R : Type*} [CommRing R]
    (A B : PowerSeries R) (hAB : A * B = 1) (s : ℕ → R) (hs0 : s 0 = 0)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A)
    (n : ℕ) :
    s n = ∑ i ∈ Finset.range (n + 1), ((n - i : ℕ) : R) * coeff (n - i) A * coeff i B ∧
    ∑ i ∈ Finset.Icc 1 n, s (n - i) * s i =
      -∑ i ∈ Finset.Icc 1 n, ((i * (n - i) : ℕ) : R) * coeff (n - i) A * coeff i B := by
  let S := PowerSeries.mk s
  let D : Derivation R (PowerSeries R) (PowerSeries R) := (X : PowerSeries R) • derivative
  have coeffD (F : PowerSeries R) (k : ℕ) : coeff k (D F) = (k : R) * coeff k F := by
    change coeff k (X * derivative F) = _
    cases k with
    | zero => simp
    | succ k => rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]
  have conv (F G : PowerSeries R) (k : ℕ) : coeff k (F * G) =
      ∑ i ∈ Finset.range (k + 1), coeff i F * coeff (k - i) G := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have convPos (F G : PowerSeries R) (k : ℕ) (hF : coeff 0 F = 0) : coeff k (F * G) =
      ∑ i ∈ Finset.Icc 1 k, coeff i F * coeff (k - i) G := by
    rw [conv, Finset.sum_range_eq_add_Ico _ (Nat.succ_pos k),
      Nat.succ_eq_add_one, Finset.Ico_add_one_right_eq_Icc, hF, zero_mul, zero_add]
  have hS0 : coeff 0 S = 0 := by simpa only [S, coeff_mk] using hs0
  have hDA : D A = S * A := by
    ext k
    simpa only [coeffD, convPos S A k hS0, S, coeff_mk] using hA k
  have hS : B * D A = S := by
    rw [hDA, mul_left_comm, mul_comm B A, hAB, mul_one]
  have hDB : A * D B = -S := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [D.leibniz, smul_eq_mul, hS, D.map_one_eq_zero] using congrArg D hAB
  have hSq : S * S = -(D B * D A) := calc
    S * S = -(A * D B) * S := by rw [hDB, neg_neg]
    _ = -(D B * D A) := by rw [hDA]; ring
  constructor
  · simpa only [conv, coeffD, S, coeff_mk, mul_comm (coeff _ B)] using congrArg (coeff n) hS.symm
  · have hDB0 : coeff 0 (D B) = 0 := by simp [coeffD]
    have h := congrArg (coeff n) hSq
    rw [map_neg, convPos S S n hS0, convPos (D B) (D A) n hDB0] at h
    simpa only [coeffD, S, coeff_mk, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h

end MetaMathlibExt
