/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Ring.Basic

/-!
# Polynomials with coefficients in an arithmetic progression

Multiplication by `(X - 1) ^ 2` cancels the interior coefficients. The identity is the
first (unnumbered) display in Lemma 1, p. 3, of
[Kakuma's paper](https://math.colgate.edu/~integers/aa92/aa92.pdf).
-/

open Polynomial

namespace MetaMathlibExt

/-- **The arithmetic-progression polynomial times $(x - 1)^2$.** For all natural numbers $m$, $a$,
$d$, the polynomial $A_m(x) = \sum_{i=0}^{m} (a + id) x^{m-i}$ satisfies, in $\mathbb{Z}[x]$,

$$A_m(x)(x - 1)^2 = a x^{m+2} - (a - d) x^{m+1} - (a + (m + 1)d) x + (a + md).$$

The source assumes $m$, $a$, $d$ positive.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 1 (`integers-2026-A92-lem-1`). -/
public theorem arithProgPoly_mul_sub_one_sq (m a d : ℕ) :
    (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) * (X - 1) ^ 2 =
      C (a : ℤ) * X ^ (m + 2) - C ((a : ℤ) - d) * X ^ (m + 1) -
        C ((a : ℤ) + (m + 1) * d) * X + C ((a : ℤ) + m * d) := by
  induction m with
  | zero =>
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, map_zero, add_zero,
      Nat.sub_zero, pow_zero, mul_one, zero_add, one_mul, map_add, map_sub, pow_one]
    ring1
  | succ m ih =>
    -- Shift the old terms by one power of X before appending the new constant term.
    have hshift :
        (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m + 1 - i)) =
          (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) * X := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hi), pow_succ, mul_assoc]
    rw [Finset.sum_range_succ, hshift, Nat.sub_self, pow_zero, mul_one, add_mul,
      mul_right_comm _ X, ih]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_sub, map_mul, map_one]
    ring1

end MetaMathlibExt
