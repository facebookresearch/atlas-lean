/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Lift
import Mathlib.Tactic.LinearCombination

/-! # Square roots modulo powers of two -/

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Square roots modulo powers of two.** For all natural numbers $m > 0$ and $n > 0$ there is
a natural number $x$ with $1 \le x \le 2^m - 1$ and $x^2 \equiv 8n + 1 \pmod{2^{m+2}}$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 3
(arXiv Lemma 3.1; `jis-2024-24.5.1-lem-3`). -/
public theorem exists_sq_modEq_eight_mul_add_one (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ x : ℕ, 1 ≤ x ∧ x ≤ 2 ^ m - 1 ∧ x ^ 2 ≡ 8 * n + 1 [MOD 2 ^ (m + 2)] := by
  -- Write the odd root as 2a + 1 and keep the signed quotient of the square error.
  have liftRoot (k : ℕ) : ∃ a q : ℤ, 0 ≤ a ∧ a < 2 ^ k ∧
      8 * (n : ℤ) + 1 - (2 * a + 1) ^ 2 = 8 * 2 ^ k * q := by
    induction k with
    | zero => exact ⟨0, n, by decide, by decide, by simp⟩
    | succ k ih =>
      obtain ⟨a, q, ha, hlt, hq⟩ := ih
      rw [pow_succ]
      obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' q
      · exact ⟨a, t, ha, by omega, by linear_combination hq⟩
      · -- Reflect about 2^(k+1). The squares differ by 8·2^k times the odd number 2·2^k-2a-1.
        refine ⟨2 * 2 ^ k - 1 - a, t + 1 + a - 2 ^ k, by omega, by omega, ?_⟩
        linear_combination hq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨a, q, ha, hlt, hq⟩ := liftRoot k
  lift a to ℕ using ha
  have hbound : a < 2 ^ k := by exact_mod_cast hlt
  refine ⟨2 * a + 1, by omega, ?_, Nat.modEq_iff_dvd.mpr ⟨q, ?_⟩⟩
  · rw [pow_succ]
    omega
  · push_cast
    rw [show k.succ + 2 = k + 3 from rfl, pow_add]
    linear_combination hq

end MetaMathlibExt
