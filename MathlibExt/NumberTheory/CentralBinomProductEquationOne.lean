/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central

/-!
# Central binomial products with shift one

Pascal's identity gives equality at `a = 1`. For positive `b`, the recurrence for central
binomial coefficients gives a larger growth factor at `a + b` than at `a`.
-/

namespace MetaMathlibExt

namespace centralBinom_add_eq_centralBinom_mul_choose_one_iff

private theorem eq_at_one (b : ℕ) :
    (1 + b).centralBinom = (1 : ℕ).centralBinom * (1 + 2 * b).choose b := by
  rw [Nat.add_comm 1 b, Nat.add_comm 1 (2 * b), show (1 : ℕ).centralBinom = 2 by rfl,
    Nat.centralBinom, show 2 * (b + 1) = 2 * b + 1 + 1 by omega,
    Nat.choose_succ_succ', Nat.choose_symm_half, ← two_mul]

private theorem lt_succ {a b c : ℕ} (hb : 0 < b)
    (h : a.centralBinom * c ≤ (a + b).centralBinom) :
    (a + 1).centralBinom * c < (a + 1 + b).centralBinom := by
  rw [Nat.succ_add]
  apply Nat.lt_of_mul_lt_mul_left (a := (a + 1) * (a + b + 1))
  calc
    _ = ((a + b + 1) * (2 * (2 * a + 1))) * (a.centralBinom * c) := by
      rw [mul_mul_mul_comm, Nat.succ_mul_centralBinom_succ]
      ac_rfl
    _ ≤ ((a + b + 1) * (2 * (2 * a + 1))) * (a + b).centralBinom :=
      Nat.mul_le_mul_left _ h
    _ < ((a + 1) * (2 * (2 * (a + b) + 1))) * (a + b).centralBinom := by
      apply Nat.mul_lt_mul_of_pos_right _ (Nat.centralBinom_pos _)
      nlinarith
    _ = _ := by
      conv_rhs => rw [mul_assoc, Nat.succ_mul_centralBinom_succ]
      ac_rfl

end centralBinom_add_eq_centralBinom_mul_choose_one_iff

open centralBinom_add_eq_centralBinom_mul_choose_one_iff

/-- **Central binomial products with $x = 1$.** Let $a$ and $b$ be positive integers. Then
$\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{1+2b}{b}$ if and only if $a = 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 2 (`integers-2026-A26-prop-2`). -/
public theorem centralBinom_add_eq_centralBinom_mul_choose_one_iff (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) :
    (a + b).centralBinom = a.centralBinom * (1 + 2 * b).choose b ↔ a = 1 := by
  have hlt (n : ℕ) (hn : 1 < n) :
      n.centralBinom * (1 + 2 * b).choose b < (n + b).centralBinom := by
    induction n, hn using Nat.le_induction with
    | base => exact lt_succ hb (eq_at_one b).ge
    | succ n _ ih => exact lt_succ hb ih.le
  obtain rfl | h := eq_or_lt_of_le (show 1 ≤ a from ha)
  · simp [eq_at_one]
  · simp [(hlt a h).ne', h.ne']

end MetaMathlibExt
