/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq

/-!
# Repetend digits under a change of base

The long-division remainder at position `j` is `m * b ^ j % n`. Adding a multiple of `n` to
the base preserves this remainder, so it is the slope of the digit as a function of the shift.
-/

namespace MetaMathlibExt

/-- **Raising the base by multiples of $n$ shifts repetend digits linearly.** Let $m$ and $j$ be
natural numbers, $n \ge 1$ and $b \ge 2$. For a base $B$ write
$d_j(B) = \lfloor m B^{j+1} / n \rfloor \bmod B$ for the $j$-th base-$B$ digit of $m/n$. Then
there is a natural number $c < n$ such that $d_j(b + tn) = d_j(b) + tc$ for every natural number
$t$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Corollary 3 (`integers-2025-A26-cor-3`). -/
public theorem digit_add_mul_modulus_eq (m n b j : ℕ) (hn : 0 < n) (hb : 2 ≤ b) :
    ∃ c < n, ∀ t : ℕ,
      m * (b + t * n) ^ (j + 1) / n % (b + t * n) = m * b ^ (j + 1) / n % b + t * c := by
  have digit (B : ℕ) (hB : 0 < B) :
      m * B ^ (j + 1) / n % B = (m * B ^ j % n) * B / n := by
    conv_lhs =>
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← Nat.mod_add_div (m * B ^ j) n, Nat.add_mul,
        Nat.mul_assoc n, Nat.add_mul_div_left _ _ hn, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul
      (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hn) hB))
  refine ⟨m * b ^ j % n, Nat.mod_lt _ hn, fun t => ?_⟩
  have hbase : b + t * n ≡ b [MOD n] := Nat.add_mul_mod_self_right b t n
  have hrem : m * (b + t * n) ^ j % n = m * b ^ j % n := (hbase.pow j).mul_left m
  rw [digit _ (by omega), digit b (by omega), hrem, Nat.mul_add, ← Nat.mul_assoc,
    Nat.add_mul_div_right _ _ hn, Nat.mul_comm _ t]

end MetaMathlibExt
