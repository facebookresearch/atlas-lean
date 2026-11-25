/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central

/-!
# Central binomial products with a bounded index sum

We prove the finite case of Meaghan Allen's central binomial product equation by checking
divisibility of the central coefficients and using monotonicity in the shift.
-/

namespace MetaMathlibExt

namespace centralBinom_add_ne_of_two_le_of_small

/-- For `2 < k < 150`, divisibility of the central coefficients rules out equality at shift
two. At shift three the product exceeds the central coefficient at `k`. -/
private theorem bounds_of_dvd : ∀ k < 150, ∀ a < k, 2 < k ∧ 0 < a →
    a.centralBinom ∣ k.centralBinom →
    let b := k - a
    k.centralBinom ≠ a.centralBinom * (2 + 2 * b).choose b ∧
      k.centralBinom < a.centralBinom * (3 + 2 * b).choose b := by
  simp only [Nat.centralBinom, Nat.choose_eq_fast_choose]
  decide +kernel

end centralBinom_add_ne_of_two_le_of_small

/-- **Central binomial products with $x \ge 2$ and $a + b < 150$.** Let $x$, $a$, $b$ be natural
numbers with $a \ge 1$, $b \ge 1$, $x \ge 2$ and $x < a + b < 150$. Then
$\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{x+2b}{b}$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 4 (`integers-2026-A26-prop-4`). -/
public theorem centralBinom_add_ne_of_two_le_of_small (x a b : ℕ) (hx : 2 ≤ x)
    (ha : 0 < a) (hb : 0 < b) (hxk : x < a + b) (hk : a + b < 150) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b := by
  intro heq
  have hdvd : a.centralBinom ∣ (a + b).centralBinom := ⟨_, heq⟩
  obtain ⟨hne, hlt⟩ := centralBinom_add_ne_of_two_le_of_small.bounds_of_dvd
    (a + b) hk a (by omega) ⟨by omega, ha⟩ hdvd
  rw [Nat.add_sub_cancel_left] at hne hlt
  rcases eq_or_lt_of_le hx with rfl | hx'
  · exact hne heq
  · exact (hlt.trans_le (Nat.mul_le_mul_left _ (Nat.choose_le_choose b (by omega)))).ne heq

end MetaMathlibExt
