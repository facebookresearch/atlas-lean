/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Rify

/-!
# Half-integer starts and odd-denominator steps
-/

namespace MetaMathlibExt

/-- **No integer points for a half-integer start and an odd denominator.** Let $s_1, s_2, p_2, q_2$
be natural numbers with $q_2$ odd, and let $x = s_1 + 1/2$ and $d = s_2 + p_2/q_2$. Then
$x + id$ is not a nonnegative integer for any natural number $i$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 22
(`integers-2026-A58-lem-22`). -/
public theorem add_mul_not_mem_nat_of_half (x d : ℝ) (s₁ s₂ p₂ q₂ : ℕ)
    (hq₂ : Nat.Coprime 2 q₂)
    (hx : x = s₁ + 1 / 2) (hd : d = s₂ + (p₂ : ℝ) / q₂) (i : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) := by
  rintro ⟨n, hn⟩
  have hodd := Nat.prime_two.coprime_iff_not_dvd.mp hq₂
  rw [hx, hd] at hn
  field_simp [show q₂ ≠ 0 by omega] at hn
  have heq : 2 * (n * q₂) = 2 * ((s₁ + i * s₂) * q₂ + i * p₂) + q₂ := by
    rify
    linear_combination hn
  omega

end MetaMathlibExt
