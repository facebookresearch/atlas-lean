/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Rify

/-!
# Rational progressions with coprime denominators
-/

namespace MetaMathlibExt

/-- **No integer points for coprime denominators, the first at least 3.** Let
$s_1, s_2, p_1, p_2, q_1, q_2$ be natural numbers with $\gcd(p_1, q_1) = 1$, $\gcd(q_1, q_2) = 1$
and $q_1 \ge 3$, and let $x = s_1 + p_1/q_1$ and $d = s_2 + p_2/q_2$. Then for all natural numbers
$i$ and $j$, neither $x + id$ nor $2x + jd$ is a nonnegative integer.

The paper's further hypotheses ($p_1, p_2, q_2 > 0$, $\gcd(p_2, q_2) = 1$, $d \notin \mathbb{N}$)
are not needed and are not stated ($p_1 > 0$ and $q_2 > 0$ already follow from the two coprimality
conditions and $q_1 \ge 3$).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem add_mul_not_mem_nat_of_coprime_den (x d : ℝ) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ)
    (hc₁ : Nat.Coprime p₁ q₁) (hq : Nat.Coprime q₁ q₂) (hq₁ : 3 ≤ q₁)
    (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂) (i j : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ) := by
  have hq₂' : q₂ ≠ 0 := by
    rintro rfl
    simp at hq
    omega
  have exclude (k t : ℕ) (hk : 0 < k) (hkq : k < q₁) :
      (k : ℝ) * x + t * d ∉ Set.range ((↑) : ℕ → ℝ) := by
    rintro ⟨n, hn⟩
    rw [hx, hd] at hn
    field_simp [show q₁ ≠ 0 by omega, hq₂'] at hn
    -- After clearing denominators, every term except k * p₁ * q₂ is a multiple of q₁.
    have heq : q₁ * ((k * s₁ + t * s₂) * q₂ + t * p₂) + k * (p₁ * q₂) = q₁ * (n * q₂) := by
      rify
      linear_combination -hn
    have hdiv : q₁ ∣ k * (p₁ * q₂) := by
      apply (Nat.dvd_add_right (Nat.dvd_mul_right q₁ _)).mp
      rw [heq]
      exact Nat.dvd_mul_right _ _
    have hdk : q₁ ∣ k := (hc₁.symm.mul_right hq).dvd_of_dvd_mul_right hdiv
    exact hkq.not_ge (Nat.le_of_dvd hk hdk)
  exact ⟨by simpa using exclude 1 i (by decide) (by omega),
    by simpa using exclude 2 j (by decide) (by omega)⟩

end MetaMathlibExt
