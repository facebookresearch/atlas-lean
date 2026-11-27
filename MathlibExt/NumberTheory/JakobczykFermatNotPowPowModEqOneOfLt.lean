/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq

/-!
# Smaller iterated powers are not congruent to one

If `a ^ b ^ n` is not congruent to `1` modulo `m`, where `2 ≤ a`, `2 ≤ b`, `2 ≤ m` and
`1 ≤ n`, then `a ^ b ^ t` is not congruent to `1` modulo `m` for any `t < n`
(`MetaMathlibExt.not_pow_pow_modEq_one_of_lt`).

This is Lemma 2 of Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat
Numbers*, INTEGERS 26 (2026), Article A77.
-/

namespace MetaMathlibExt

-- The bounds on `a`, `b`, `m` and `n` are not needed for the implication: raising the
-- congruence to `b ^ (n - t)` only uses `t < n`.
set_option linter.unusedVariables false in
/-- **Smaller iterated powers are not congruent to one.** Let $a, b, m \ge 2$ and $n \ge 1$ be
natural numbers with $a^{b^n} \not\equiv 1 \pmod m$. Then $a^{b^t} \not\equiv 1 \pmod m$ for every
natural number $t < n$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Lemma 2 (`integers-2026-A77-lem-2`). -/
public theorem not_pow_pow_modEq_one_of_lt {a b m n t : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hm : 2 ≤ m) (hn : 1 ≤ n) (h : ¬ a ^ b ^ n ≡ 1 [MOD m]) (ht : t < n) :
    ¬ a ^ b ^ t ≡ 1 [MOD m] := by
  intro hcon
  apply h
  have hexp : b ^ t * b ^ (n - t) = b ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' ht.le]
  have hpow := Nat.ModEq.pow (b ^ (n - t)) hcon
  rwa [one_pow, ← pow_mul, hexp] at hpow

end MetaMathlibExt
