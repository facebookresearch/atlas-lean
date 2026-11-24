/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq

/-!
# Differences of repetend digits

`MetaMathlibExt.repetend_digit_sub_eq` expresses the signed difference of two digits of
`1 / n` in terms of the remainders before and after their long-division steps.
-/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Differences of repetend digits.** Let $n \ge 1$ and $b$ be natural numbers with
$\gcd(b, n) = 1$. For $x, j \ge 0$ put $b_x = b^x \bmod n$ and
$r_{x,j} = \lfloor b_x^{j+1}/n \rfloor \bmod b_x$. Then for all natural numbers $y, m, d, e$,
$$n (r_{ym,e} - r_{y,d}) = b_{ym} b_{yme} - b_{ym(e+1)} - b_y b_{yd} + b_{y(d+1)}.$$

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 7 (`integers-2025-A26-lem-7`). -/
public theorem repetend_digit_sub_eq (n b y m d e : ℕ) (hn : 0 < n) (hb : Nat.Coprime b n) :
    let r : ℕ → ℕ → ℕ := fun x j => (b ^ x % n) ^ (j + 1) / n % (b ^ x % n)
    (n : ℤ) * ((r (y * m) e : ℤ) - r y d) =
      ((b ^ (y * m) % n : ℕ) : ℤ) * (b ^ (y * m * e) % n : ℕ) -
        (b ^ (y * m * (e + 1)) % n : ℕ) -
        ((b ^ y % n : ℕ) : ℤ) * (b ^ (y * d) % n : ℕ) + (b ^ (y * (d + 1)) % n : ℕ) := by
  intro r
  let B (x : ℕ) := b ^ x % n
  have hpow (x j : ℕ) : B x ^ j % n = B (x * j) := by
    simp only [B, pow_mul, ← Nat.pow_mod]
  have step (x j : ℕ) :
      (n : ℤ) * r x j + B (x * (j + 1)) = (B x : ℤ) * B (x * j) := by
    have digit : r x j = B x * B (x * j) / n := by
      change B x ^ (j + 1) / n % B x = _
      rw [← Nat.mod_mul_left_div_self, pow_succ', Nat.mul_mod_mul_left, hpow]
    have rem : B x * B (x * j) % n = B (x * (j + 1)) := by
      rw [← hpow x (j + 1), ← hpow x j, pow_succ', Nat.mul_mod_mod]
    rw [digit, ← rem]
    exact_mod_cast Nat.div_add_mod (B x * B (x * j)) n
  have h₁ := step (y * m) e
  have h₂ := step y d
  dsimp only [B] at h₁ h₂
  rw [Int.mul_sub]
  omega

end MetaMathlibExt
