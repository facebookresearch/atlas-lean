/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MotzkinHumpsYoungTableaux
import MathlibExt.Combinatorics.Enumerative.AdjustedSytHookCount
import Mathlib.Tactic.LinearCombination

/-!
# Generating function for hook tableau counts

For a fixed first-two-row difference $k$, multiplying the generating function of the
$(2,1)$-hook tableau counts by $1 + x$ gives $x^k (1 + x M(x)^{k+1})$, where $M$ is the
Motzkin series (`sytHookCount_generatingFunction`). The proof clears the alternating correction
from the generating function of the adjusted counts.
-/

namespace MetaMathlibExt

namespace sytHookCount_generatingFunction

open PowerSeries

-- Multiplying the alternating correction series by `1 + X` leaves `-X ^ k`.
private theorem one_add_X_mul_correction (k : ℕ) :
    (1 + (X : PowerSeries ℤ)) * mk (fun n => if k ≤ n then (-1 : ℤ) ^ (n + k + 1) else 0) =
      -X ^ k := by
  ext n
  rw [add_mul, one_mul, map_add, map_neg, coeff_X_pow]
  cases n with
  | zero => cases k <;> simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_mk, coeff_mk]
    obtain h | rfl | h := lt_trichotomy (n + 1) k
    · simp [Nat.not_le_of_gt h, show ¬k ≤ n by omega, h.ne]
    · simp [pow_succ, pow_add, ← mul_pow]
    · simp [h.le, show k ≤ n by omega, h.ne',
        show n + 1 + k + 1 = (n + k + 1) + 1 by omega, pow_succ]

-- The adjusted series is the tableau series plus the alternating correction series.
private theorem adjusted_eq_add (k : ℕ) :
    mk (fun n => if k ≤ n then (sytHookCount n k : ℤ) + (-1 : ℤ) ^ (n + k + 1) else 0) =
      mk (fun n => if k ≤ n then (sytHookCount n k : ℤ) else 0) +
        mk (fun n => if k ≤ n then (-1 : ℤ) ^ (n + k + 1) else 0) := by
  ext n
  simp only [map_add, coeff_mk]
  split_ifs <;> simp

end sytHookCount_generatingFunction

open sytHookCount_generatingFunction

/-- **Generating function for hook tableau counts.** For a natural number $k$, let
$\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux of order $n$ in the
$(2,1)$-hook whose first row is longer than its second row by exactly $k$, and let
$M(x) = \sum_{n \ge 0} m_n x^n$ be the generating function of the Motzkin numbers $m_n$. Then,
in the ring of formal power series with integer coefficients,
$$
(1 + x) \sum_{n \ge k} \mathrm{SYT}_k(2,1;n)\, x^n = x^k \bigl(1 + x\, M(x)^{k+1}\bigr).
$$

The factor $1 + x$ is cleared, so the identity involves no division.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Corollary 9 (`jis-2025-25.8.1-cor-9`).
-/
public theorem sytHookCount_generatingFunction (k : ℕ) :
    (1 + (PowerSeries.X : PowerSeries ℤ)) *
        PowerSeries.mk (fun n => if k ≤ n then (sytHookCount n k : ℤ) else 0) =
      PowerSeries.X ^ k * (1 + PowerSeries.X * motzkinSeries ^ (k + 1)) := by
  have h := adjustedSytHookCount_generatingFunction k
  rw [adjusted_eq_add, mul_add, one_add_X_mul_correction] at h
  linear_combination h

end MetaMathlibExt
