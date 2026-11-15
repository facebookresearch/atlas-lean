/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

/-!
# Gödel's beta function

`β c d i = c % (1 + (i + 1) * d)`. The value is below its
modulus, and any two values are coded by some `c, d` (the
moduli `1 + d` and `1 + 2d` are coprime, so CRT applies).
Coding of arbitrary finite sequences is not included here.
-/

@[expose] public section

/-- Gödel's beta function (core of VER-44):
`β c d i = c % (1 + (i+1) * d)`. -/
def beta (c d i : ℕ) : ℕ := c % (1 + (i + 1) * d)

/-- The beta value is below its modulus. -/
theorem beta_lt (c d i : ℕ) : beta c d i < 1 + (i + 1) * d := by
  unfold beta
  exact Nat.mod_lt c (by omega)

/-- The CRT moduli `1 + d` and `1 + 2 * d` are coprime. -/
private theorem coprime_beta_moduli (d : ℕ) : Nat.Coprime (1 + d) (1 + 2 * d) := by
  have h1 : 1 + 2 * d = (1 + d) + d := by ring
  rw [h1, Nat.coprime_self_add_right, Nat.add_comm 1 d, Nat.coprime_self_add_left]
  exact Nat.coprime_one_left d

/-- Beta codes any two values: there are `c d` with
`β c d 0 = a` and `β c d 1 = b`. (By CRT for the coprime
moduli `1 + d` and `1 + 2d` with `d` chosen so both exceed
`a, b` and are coprime: any `d` with `1 + d > max a b`... the
standard choice keeps `gcd (1+d) (1+2d) = gcd (1+d) d = 1`
when `d` is a multiple of... use `d = (a+b+2)! `-free route:
`Nat.chineseRemainder` needs coprimality
`Nat.Coprime (1 + d) (1 + 2 * d)`, which holds iff
`Nat.Coprime (1 + d) d`, e.g. taking the moduli as
`m₀ = 1 + d`, `m₁ = 1 + 2 * d` with `d` arbitrary gives
`gcd ∣ d` and `gcd ∣ 1 + d` hence `gcd ∣ 1` after using
`1 + 2d = 2(1+d) - d`... in any case provable for all `d`.) -/
theorem beta_codes_pair (a b : ℕ) :
    ∃ c d : ℕ, beta c d 0 = a ∧ beta c d 1 = b := by
  have ha : a < 1 + (a + b + 1) := by omega
  have hb : b < 1 + 2 * (a + b + 1) := by omega
  have hcop : Nat.Coprime (1 + (a + b + 1)) (1 + 2 * (a + b + 1)) :=
    coprime_beta_moduli _
  obtain ⟨c, hc0, hc1⟩ := Nat.chineseRemainder hcop a b
  refine ⟨c, a + b + 1, ?_, ?_⟩
  · show c % (1 + (0 + 1) * (a + b + 1)) = a
    have hmod : (1 : ℕ) + (0 + 1) * (a + b + 1) = 1 + (a + b + 1) := by ring
    rw [hmod]
    have h0 : c % (1 + (a + b + 1)) = a % (1 + (a + b + 1)) := hc0
    exact h0.trans (Nat.mod_eq_of_lt ha)
  · show c % (1 + (1 + 1) * (a + b + 1)) = b
    have hmod : (1 : ℕ) + (1 + 1) * (a + b + 1) = 1 + 2 * (a + b + 1) := by ring
    rw [hmod]
    have h1 : c % (1 + 2 * (a + b + 1)) = b % (1 + 2 * (a + b + 1)) := hc1
    exact h1.trans (Nat.mod_eq_of_lt hb)

end
