/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Power identity at roots of an arithmetic-progression polynomial

Multiplying the evaluated sum by `(z - 1) ^ 2` leaves only the boundary terms.
-/

open Polynomial

namespace MetaMathlibExt

private theorem sum_mul_sub_one_sq (m : ℕ) (a d z : ℂ) :
    (∑ i ∈ Finset.range (m + 1), (a + i * d) * z ^ (m - i)) * (z - 1) ^ 2 =
      z ^ (m + 1) * (a * z - (a - d)) - ((a + (m + 1) * d) * z - (a + m * d)) := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    have hshift :
        (∑ i ∈ Finset.range (m + 1), (a + i * d) * z ^ (m + 1 - i)) =
          (∑ i ∈ Finset.range (m + 1), (a + i * d) * z ^ (m - i)) * z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hi), pow_succ, mul_assoc]
    rw [Finset.sum_range_succ, hshift, Nat.sub_self, pow_zero, mul_one, Nat.cast_succ, pow_succ]
    linear_combination z * ih

/-- **Power identity at the roots of an arithmetic-progression polynomial.** Let $m$ and $a$
be natural numbers, let $d$ be a positive integer, and let
$A_m(x) = a x^m + (a + d) x^{m-1} + \cdots + (a + md)$, that is,
$A_m(x) = \sum_{i=0}^{m} (a + id) x^{m-i} \in \mathbb{Z}[x]$. If $z \in \mathbb{C}$ is a root of
$A_m$ or $z = 1$, then

$$z^{m+1} = \frac{(a + (m + 1)d) z - (a + md)}{a z - (a - d)}.$$

With the paper's notation $a_n = a + (n - 1)d$ this reads
$z^{m+1} = (a_{m+2} z - a_{m+1}) / (a_1 z - a_0)$. The denominator does not vanish at such $z$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 1, equation (2)
(`integers-2026-A92-lem-1`). -/
public theorem arithProgPoly_root_pow_eq (m a d : ℕ) (hd : 0 < d) (z : ℂ)
    (hz : aeval z (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) = 0 ∨ z = 1) :
    z ^ (m + 1) =
      (((a : ℂ) + (m + 1) * d) * z - ((a : ℂ) + m * d)) / ((a : ℂ) * z - ((a : ℂ) - d)) := by
  have hprod := sum_mul_sub_one_sq m a d z
  have hzero : (∑ i ∈ Finset.range (m + 1), ((a : ℂ) + i * d) * z ^ (m - i)) *
      (z - 1) ^ 2 = 0 := by
    rcases hz with hroot | rfl
    · exact mul_eq_zero_of_left (by simpa using hroot) _
    · simp
  have hcross := sub_eq_zero.mp (hprod.symm.trans hzero)
  apply (eq_div_iff _).2 hcross
  intro hden
  rw [hden, mul_zero] at hcross
  have hdet : ((m : ℂ) + 1) * (d : ℂ) ^ 2 = 0 := by
    linear_combination ((a : ℂ) + (m + 1) * d) * hden + a * hcross
  have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast m.succ_ne_zero
  exact mul_ne_zero hm (pow_ne_zero _ (Nat.cast_ne_zero.mpr hd.ne')) hdet

end MetaMathlibExt
