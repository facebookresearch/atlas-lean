/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst

/-!
# Signed Stirling numbers and the falling factorial

The falling factorial expands in powers of `X` with the signed Stirling numbers of the first
kind as coefficients.
-/

namespace MetaMathlibExt

open Polynomial

/-- **Falling factorial in terms of signed Stirling numbers.** For every natural number $n$, the
identity of polynomials with integer coefficients
$$x (x - 1) \cdots (x - n + 1) = \sum_{k=0}^{n} s(n, k)\, x^k$$
holds, where $s(n, k)$ is the signed Stirling number of the first kind.

Source: Benjamin Schreyer, *Rigged Horse Numbers and their Modular Periodicity*, Journal of
Integer Sequences 28 (2025), Article 25.4.1, Proposition 2 (`jis-2025-25.4.1-prop-2`). -/
public theorem descPochhammer_eq_sum_signedStirlingFirst (n : ℕ) :
    descPochhammer ℤ n =
      ∑ k ∈ Finset.range (n + 1), C (signedStirlingFirst n k) * X ^ k := by
  have hcoeff (k : ℕ) : (descPochhammer ℤ n).coeff k = signedStirlingFirst n k := by
    induction n generalizing k with
    | zero => cases k <;> simp [coeff_one, signedStirlingFirst_eq_zero_of_lt]
    | succ n ih =>
      cases k with
      | zero => simp [descPochhammer_succ_left]
      | succ k =>
        rw [descPochhammer_succ_right, ← C_eq_natCast, coeff_mul_X_sub_C, ih, ih,
          signedStirlingFirst_succ_succ, mul_comm]
  simpa only [descPochhammer_natDegree, hcoeff] using
    (descPochhammer ℤ n).as_sum_range_C_mul_X_pow

end MetaMathlibExt
