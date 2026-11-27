/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.CentralBinomProductEquationOne

/-!
# Central binomial products in the case `x = a - 2`

At `a = 3` the shift is one, so the shift-one equality criterion applies. At `a = 4`
a factorial comparison gives a strict inequality, which persists as `a` increases with `b` fixed.
-/

namespace MetaMathlibExt

namespace centralBinom_add_ne_centralBinom_mul_choose_sub_two

private theorem lt_at_four (b : ℕ) (hb : 0 < b) :
    (4 + b).centralBinom < (4 : ℕ).centralBinom * (4 + 2 * b - 2).choose b := by
  rw [show 4 + 2 * b - 2 = 2 * b + 2 by omega]
  let den := (b + 1) * (b + 3) * (b + 4)
  let num := 8 * (2 * b + 3) * (2 * b + 5) * (2 * b + 7)
  let f := (b + 2).factorial * b.factorial * (b + 2) * (b + 3) * (b + 4)
  have hf : 0 < f := by dsimp [f]; positivity
  have hden : 0 < den := by dsimp [den]; positivity
  have hc := Nat.choose_mul_factorial_mul_factorial (show b + 4 ≤ 2 * (b + 4) by omega)
  rw [show 2 * (b + 4) - (b + 4) = b + 4 by omega, ← Nat.centralBinom,
    show 2 * (b + 4) = 2 * b + 8 by omega] at hc
  have hchoose := Nat.choose_mul_factorial_mul_factorial (show b ≤ 2 * b + 2 by omega)
  rw [show 2 * b + 2 - b = b + 2 by omega] at hchoose
  have htwo : (b + 2).factorial = (b + 2) * ((b + 1) * b.factorial) := by
    rw [Nat.factorial_succ (b + 1), Nat.factorial_succ b]
  have hfour : (b + 4).factorial = (b + 4) * ((b + 3) * (b + 2).factorial) := by
    rw [Nat.factorial_succ (b + 3), Nat.factorial_succ (b + 2)]
  have hratio : (4 + b).centralBinom * den = (2 * b + 2).choose b * num := by
    apply mul_left_cancel₀ hf.ne'
    calc
      _ = (b + 4).centralBinom * (b + 4).factorial * (b + 4).factorial := by
        dsimp [f, den]
        rw [Nat.add_comm 4 b, hfour, htwo]
        ring
      _ = (2 * b + 8).factorial := hc
      _ = _ := by
        rw [Nat.factorial_succ (2 * b + 7), Nat.factorial_succ (2 * b + 6),
          Nat.factorial_succ (2 * b + 5), Nat.factorial_succ (2 * b + 4),
          Nat.factorial_succ (2 * b + 3), Nat.factorial_succ (2 * b + 2), ← hchoose]
        dsimp [f, num]
        ring
  have hnum : num < 70 * den := by
    calc
      num < num + (6 * b ^ 3 + 80 * b ^ 2 + 194 * b) := by
        exact Nat.lt_add_of_pos_right (by positivity)
      _ = 70 * den := by dsimp [num, den]; ring
  apply (mul_lt_mul_iff_left₀ hden).1
  calc
    _ = (2 * b + 2).choose b * num := hratio
    _ < (2 * b + 2).choose b * (70 * den) :=
      Nat.mul_lt_mul_of_pos_left hnum (Nat.choose_pos (by omega))
    _ = ((4 : ℕ).centralBinom * (2 * b + 2).choose b) * den := by
      rw [show (4 : ℕ).centralBinom = 70 by decide]
      ac_rfl

private theorem lt_succ {a b : ℕ} (ha : 4 ≤ a) (hb : 0 < b)
    (h : (a + b).centralBinom ≤ a.centralBinom * (a + 2 * b - 2).choose b) :
    (a + 1 + b).centralBinom < (a + 1).centralBinom * (a + 1 + 2 * b - 2).choose b := by
  let k := a + b
  let n := a + 2 * b - 2
  change k.centralBinom ≤ a.centralBinom * n.choose b at h
  rw [show a + 1 + b = k + 1 by dsimp [k]; omega,
    show a + 1 + 2 * b - 2 = n + 1 by dsimp [n]; omega]
  have hchoose : n.choose b * (n + 1) = (n + 1).choose b * (k - 1) := by
    rw [Nat.choose_mul_succ_eq, show n + 1 - b = k - 1 by dsimp [n, k]; omega]
  have hgrowth : (a + 1) * (k - 1) * (2 * k + 1) < (k + 1) * (2 * a + 1) * (n + 1) := by
    calc
      _ < (a + 1) * (k - 1) * (2 * k + 1) + 2 * b * (a * (k + 1) + 1) := by
        exact Nat.lt_add_of_pos_right (by positivity)
      _ = _ := by
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' ha
        dsimp [k, n]
        rw [show c + 4 + b - 1 = c + b + 3 by omega,
          show c + 4 + 2 * b - 2 = c + 2 * b + 2 by omega]
        ring
  apply Nat.lt_of_mul_lt_mul_left (a := (a + 1) * (k - 1) * (k + 1))
  calc
    _ = 2 * ((a + 1) * (k - 1) * (2 * k + 1)) * k.centralBinom := by
      rw [mul_assoc, Nat.succ_mul_centralBinom_succ]
      ac_rfl
    _ < 2 * ((k + 1) * (2 * a + 1) * (n + 1)) * k.centralBinom :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hgrowth (by decide))
        (Nat.centralBinom_pos k)
    _ ≤ 2 * ((k + 1) * (2 * a + 1) * (n + 1)) * (a.centralBinom * n.choose b) :=
      Nat.mul_le_mul_left _ h
    _ = (k + 1) * (2 * (2 * a + 1) * a.centralBinom) * (n.choose b * (n + 1)) := by
      ac_rfl
    _ = _ := by rw [← Nat.succ_mul_centralBinom_succ, hchoose]; ac_rfl

end centralBinom_add_ne_centralBinom_mul_choose_sub_two

/-- **Central binomial products in the case $x = a - 2$.** Let $a$ and $b$ be natural numbers
with $4 < 2a \le a + b$. Then $\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{a+2b-2}{b}$, so the
equation $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ has no solution with $x = a - 2$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 3 (`integers-2026-A26-lem-3`). -/
public theorem centralBinom_add_ne_centralBinom_mul_choose_sub_two (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 2).choose b := by
  have hb : 0 < b := by omega
  obtain rfl | ha' := (show 3 ≤ a by omega).eq_or_lt
  · rw [show 3 + 2 * b - 2 = 1 + 2 * b by omega]
    exact fun h => (by decide : (3 : ℕ) ≠ 1)
      ((centralBinom_add_eq_centralBinom_mul_choose_one_iff 3 b (by decide) hb).1 h)
  · apply ne_of_lt
    clear ha hab
    induction a, ha' using Nat.le_induction with
    | base => exact centralBinom_add_ne_centralBinom_mul_choose_sub_two.lt_at_four b hb
    | succ a ha ih =>
      exact centralBinom_add_ne_centralBinom_mul_choose_sub_two.lt_succ ha hb ih.le

end MetaMathlibExt
