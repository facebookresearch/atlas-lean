/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central

/-!
# Central binomial products in the case `x = a - 1`

For fixed `a ≥ 3`, the two sides agree at `b = 0`. The binomial recurrences show that
increasing `b` multiplies the product by a strictly larger factor than the central coefficient.
-/

namespace MetaMathlibExt

namespace centralBinom_add_ne_centralBinom_mul_choose_sub_one

private theorem lt_succ {a b : ℕ} (ha : 3 ≤ a)
    (h : (a + b).centralBinom ≤ a.centralBinom * (a + 2 * b - 1).choose b) :
    (a + (b + 1)).centralBinom < a.centralBinom * (a + 2 * (b + 1) - 1).choose (b + 1) := by
  let k := a + b
  let n := a + 2 * b - 1
  change k.centralBinom ≤ a.centralBinom * n.choose b at h
  rw [show a + (b + 1) = k + 1 by omega,
    show a + 2 * (b + 1) - 1 = n + 2 by dsimp [n]; omega]
  have hchoose : (n + 2).choose (b + 1) * ((b + 1) * k) = n.choose b * ((n + 1) * (n + 2)) := by
    rw [← mul_assoc, ← Nat.add_one_mul_choose_eq, mul_assoc,
      show k = n + 1 - b by dsimp [k, n]; omega, ← Nat.choose_mul_succ_eq]
    ac_rfl
  have hgrowth : (b + 1) * k * (2 * (2 * k + 1)) < (k + 1) * ((n + 1) * (n + 2)) := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' ha
    dsimp [k, n]
    rw [show c + 3 + 2 * b - 1 = c + 2 + 2 * b by omega]
    ring_nf
    omega
  apply Nat.lt_of_mul_lt_mul_left (a := (b + 1) * k * (k + 1))
  calc
    _ = ((b + 1) * k * (2 * (2 * k + 1))) * k.centralBinom := by
      rw [mul_assoc, Nat.succ_mul_centralBinom_succ]
      ac_rfl
    _ < ((k + 1) * ((n + 1) * (n + 2))) * k.centralBinom :=
      Nat.mul_lt_mul_of_pos_right hgrowth (Nat.centralBinom_pos k)
    _ ≤ ((k + 1) * ((n + 1) * (n + 2))) * (a.centralBinom * n.choose b) :=
      Nat.mul_le_mul_left _ h
    _ = ((k + 1) * a.centralBinom) * (n.choose b * ((n + 1) * (n + 2))) := by ac_rfl
    _ = _ := by rw [← hchoose]; ac_rfl

end centralBinom_add_ne_centralBinom_mul_choose_sub_one

open centralBinom_add_ne_centralBinom_mul_choose_sub_one

/-- **Central binomial products in the case $x = a - 1$.** Let $a$ and $b$ be natural numbers
with $4 < 2a \le a + b$. Then $\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{a+2b-1}{b}$, so the
equation $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ has no solution with $x = a - 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 2 (`integers-2026-A26-lem-2`). -/
public theorem centralBinom_add_ne_centralBinom_mul_choose_sub_one (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 1).choose b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ b by omega)
  apply ne_of_lt
  clear hab
  induction m with
  | zero => exact lt_succ (by omega) (by simp)
  | succ m ih => exact lt_succ (by omega) ih.le

end MetaMathlibExt
