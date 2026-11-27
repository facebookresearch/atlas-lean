/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The last digit of a repetend

The final digit of the base-`b` repetend of `1/n` is nonzero when `b` and `n` are coprime.
-/

namespace MetaMathlibExt

/-- **The last repetend digit is nonzero.** Let $n \ge 2$ and let $b \ge 2$ be prime to $n$,
with multiplicative order $L$ modulo $n$ (the repetend length of $1/n$ in base $b$). Then the
digit $\lfloor b^{(L-1)+1}/n \rfloor \bmod b$ of $1/n$ at position $L - 1$ is not $0$.

This holds for every such base, not only for the small bases $b < n$ that form the rows of the
paper's table.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 25 (`integers-2025-A26-lem-25`). -/
public theorem repetend_last_digit_ne_zero (n b : ℕ) (hn : 2 ≤ n) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b n) :
    b ^ (orderOf (b : ZMod n) - 1 + 1) / n % b ≠ 0 := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime b n).mpr hcop
  have horder : 0 < orderOf (b : ZMod n) := by
    rw [← hu, orderOf_units]
    exact orderOf_pos u
  rw [Nat.sub_add_cancel horder]
  have hpow : ((b ^ orderOf (b : ZMod n) : ℕ) : ZMod n) = 1 := by
    rw [Nat.cast_pow, pow_orderOf_eq_one]
  have hrem : b ^ orderOf (b : ZMod n) % n = 1 := by
    have : Fact (1 < n) := ⟨hn⟩
    simpa only [ZMod.val_natCast, ZMod.val_one] using congrArg ZMod.val hpow
  intro hzero
  have hmul : b ∣ n * (b ^ orderOf (b : ZMod n) / n) :=
    dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero hzero) n
  have hdvd : b ∣ b ^ orderOf (b : ZMod n) := dvd_pow_self b horder.ne'
  rw [← Nat.mod_add_div (b ^ orderOf (b : ZMod n)) n, hrem] at hdvd
  have hone : b ∣ 1 := (Nat.dvd_add_iff_left hmul).mpr hdvd
  exact (by omega : b ≠ 1) (Nat.dvd_one.mp hone)

end MetaMathlibExt
