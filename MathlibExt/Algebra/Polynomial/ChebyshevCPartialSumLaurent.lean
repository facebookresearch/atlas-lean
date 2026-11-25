/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Polynomial.Dickson
public import MathlibExt.Algebra.Polynomial.ChebyshevCPartialSum

/-! # Laurent polynomial identity for the monic Chebyshev partial sums -/

open LaurentPolynomial Polynomial

namespace MetaMathlibExt

/-- **Laurent polynomial identity for the partial sums of Chebyshev polynomials.** Let
$F_r = 1 + \sum_{k=1}^{r} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every natural number $r$, in the ring $\mathbb{Z}[q, q^{-1}]$ of Laurent polynomials,
$$q^{r+1} + q^{-r-1} - q^r - q^{-r} = q^{-1} (q - 1)^2 F_r(q + q^{-1}).$$

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Lemma 6.1
(`jis-2026-26.4.4-lem-26`). -/
public theorem chebyshevCPartialSum_laurent_identity (r : ℕ) :
    (LaurentPolynomial.T ((r : ℤ) + 1) + LaurentPolynomial.T (-(r : ℤ) - 1) -
        LaurentPolynomial.T (r : ℤ) - LaurentPolynomial.T (-(r : ℤ)) : LaurentPolynomial ℤ) =
      LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 - 1) ^ 2 *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (chebyshevCPartialSum r) := by
  have hpoly : Chebyshev.C ℤ (r + 1 : ℕ) - Chebyshev.C ℤ r =
      (X - 2) * chebyshevCPartialSum r := by
    cases r with
    | zero => simp [chebyshevCPartialSum_zero]
    | succ r =>
      have hrec := chebyshevCPartialSum_recurrence (r + 1) (Nat.le_add_left 1 r)
      rw [Nat.add_sub_cancel] at hrec
      linear_combination hrec - chebyshevCPartialSum_succ (r + 1) + chebyshevCPartialSum_succ r
  have hinv : (T 1 * T (-1) : LaurentPolynomial ℤ) = 1 := by
    rw [← T_add]
    exact T_zero
  have heval (n : ℕ) : aeval (T 1 + T (-1) : LaurentPolynomial ℤ) (Chebyshev.C ℤ n) =
      T (n : ℤ) + T (-(n : ℤ)) := by
    rw [Chebyshev.aeval_C, ← dickson_one_one_eq_chebyshev_C, dickson_one_one_eval_add_inv _ _ hinv]
    simp [T_pow]
  have hfactor : (T (-1) * (T 1 - 1) ^ 2 : LaurentPolynomial ℤ) = T 1 + T (-1) - 2 := by
    linear_combination (T 1 - 2) * hinv
  have h := congrArg (aeval (T 1 + T (-1) : LaurentPolynomial ℤ)) hpoly
  rw [map_sub, heval, heval, map_mul, map_sub, aeval_X, map_ofNat] at h
  rw [hfactor]
  simpa only [Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg, add_assoc] using h

end MetaMathlibExt
