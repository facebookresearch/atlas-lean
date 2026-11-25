/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination

/-!
# Linear Diophantine equations

Given Bézout coefficients `u, v` for `a, b`, the parameter of a solution `(x, y)` of
`a * x + b * y + c = 0` is `v * x - u * y`.
-/

namespace MetaMathlibExt

/-- **Linear Diophantine equations.** Let $a, b, c, u, v \in \mathbb{Z}$ with $a \ne 0$ or
$b \ne 0$, let $d = \gcd(a, b)$, and suppose $a u + b v = d$ (Bézout). If $d \mid c$, then the
integers $x, y$ with $a x + b y + c = 0$ are exactly those of the form
$x = -(c/d) u + m (b/d)$, $y = -(c/d) v - m (a/d)$ with $m \in \mathbb{Z}$. If $d \nmid c$, then
$a x + b y + c = 0$ has no solution in integers $x, y$.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Proposition 1. -/
public theorem linear_diophantine_solutions (a b c u v : ℤ) (hab : a ≠ 0 ∨ b ≠ 0)
    (huv : a * u + b * v = Int.gcd a b) :
    ((Int.gcd a b : ℤ) ∣ c → ∀ x y : ℤ, a * x + b * y + c = 0 ↔
      ∃ m : ℤ, x = -(c / Int.gcd a b) * u + m * (b / Int.gcd a b) ∧
        y = -(c / Int.gcd a b) * v - m * (a / Int.gcd a b)) ∧
    (¬ (Int.gcd a b : ℤ) ∣ c → ∀ x y : ℤ, a * x + b * y + c ≠ 0) := by
  have hd : (Int.gcd a b : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Int.gcd_pos_iff.mpr hab).ne'
  have ha := Int.gcd_dvd_left a b
  have hb := Int.gcd_dvd_right a b
  generalize (Int.gcd a b : ℤ) = d at *
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hbez : a' * u + b' * v = 1 := by
    apply mul_left_cancel₀ hd
    simpa only [mul_add, ← mul_assoc, mul_one] using huv
  constructor
  · rintro ⟨c', rfl⟩ x y
    simp only [Int.mul_ediv_cancel_left _ hd]
    rw [mul_assoc d a', mul_assoc d b', ← mul_add, ← mul_add, mul_eq_zero, or_iff_right hd]
    constructor
    · intro hxy
      refine ⟨v * x - u * y, ?_, ?_⟩
      · linear_combination u * hxy - x * hbez
      · linear_combination v * hxy - y * hbez
    · rintro ⟨m, rfl, rfl⟩
      linear_combination -c' * hbez
  · intro hc x y hxy
    apply hc
    exact ⟨-(a' * x + b' * y), by linear_combination hxy⟩

end MetaMathlibExt
