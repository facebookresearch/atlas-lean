/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.ModEq
import Mathlib.Order.Filter.Cofinite
import Mathlib.Tactic.WLOG

/-!
# Intersections of arithmetic progressions in the natural numbers

Let `g` be the gcd of the original steps. A common term shows that `g` divides the gap between
the chosen terms. Starting at those terms, take every `gap / g`-th term of each progression.
The new steps have gcd equal to the gap, so the Chinese remainder theorem gives arbitrarily
large common terms congruent to both chosen terms modulo the gap.
-/

open Filter

namespace MetaMathlibExt

private theorem natProgression_inter_infinite.frequently_common_terms {a b m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hab : a ≡ b [MOD m.gcd n]) :
    ∃ᶠ x in atTop, (∃ i : ℕ, x = a + m * i) ∧ ∃ j : ℕ, x = b + n * j := by
  obtain ⟨r, hrm, hrn⟩ := Nat.chineseRemainder' hab
  have hfreq := Nat.frequently_modEq (Nat.lcm_ne_zero hm hn) r
  refine (hfreq.and_eventually (eventually_ge_atTop (max a b))).mono ?_
  rintro x ⟨hx, hle⟩
  exact ⟨(Nat.modEq_iff_exists_eq_add ((le_max_left a b).trans hle)).mp
      ((hx.of_dvd (Nat.dvd_lcm_left m n)).trans hrm).symm,
    (Nat.modEq_iff_exists_eq_add ((le_max_right a b).trans hle)).mp
      ((hx.of_dvd (Nat.dvd_lcm_right m n)).trans hrn).symm⟩

/-- **Two intersecting progressions share infinitely many terms with a third.** Let
$a_1, a_2, d_1, d_2, a, b$ be natural numbers with $d_1, d_2 > 0$, where
$\mathbb{N} = \{0, 1, 2, \dots\}$, and let $P_i = \{a_i + d_i n : n \in \mathbb{N}\}$ for
$i = 1, 2$. If $a \in P_1$, $b \in P_2$, $P_1 \cap P_2$ is nonempty and $a \neq b$, then
$P_1 \cap P_2$ contains infinitely many elements of the progression
$\{\min(a, b) + |a - b|\, n : n \in \mathbb{N}\}$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 9 (`integers-2025-A41-lem-9`). -/
public theorem natProgression_inter_infinite (a₁ a₂ d₁ d₂ a b : ℕ) (hd₁ : 0 < d₁)
    (hd₂ : 0 < d₂) (ha : ∃ n : ℕ, a = a₁ + d₁ * n) (hb : ∃ n : ℕ, b = a₂ + d₂ * n)
    (hne : ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} : Set ℕ).Nonempty)
    (hab : a ≠ b) :
    ({x | ∃ n : ℕ, x = a₁ + d₁ * n} ∩ {x | ∃ n : ℕ, x = a₂ + d₂ * n} ∩
      {x | ∃ n : ℕ, x = min a b + (max a b - min a b) * n} : Set ℕ).Infinite := by
  wlog hlt : a < b generalizing a₁ a₂ d₁ d₂ a b
  · simpa only [Set.inter_comm, min_comm, max_comm] using
      this a₂ a₁ d₂ d₁ b a hd₂ hd₁ hb ha (by simpa only [Set.inter_comm] using hne)
        hab.symm (by omega)
  rw [min_eq_left hlt.le, max_eq_right hlt.le]
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  obtain ⟨c, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hne
  have hac : a ≡ c [MOD d₁] := by simp [hi, hu]
  have hcb : c ≡ b [MOD d₂] := by simp [hv, hj]
  have hg := (hac.of_dvd (Nat.gcd_dvd_left d₁ d₂)).trans (hcb.of_dvd (Nat.gcd_dvd_right d₁ d₂))
  obtain ⟨k, hk⟩ := hg.dvd'
  have hk₀ : k ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hk
    omega
  have hscaled : a ≡ b [MOD (d₁ * k).gcd (d₂ * k)] := by
    rw [Nat.gcd_mul_right, Nat.modEq_iff_dvd' hlt.le, hk]
  have hfreq := natProgression_inter_infinite.frequently_common_terms
    (Nat.mul_ne_zero hd₁.ne' hk₀) (Nat.mul_ne_zero hd₂.ne' hk₀) hscaled
  apply Nat.frequently_atTop_iff_infinite.mp
  refine hfreq.mono ?_
  rintro x ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  have hdiv : b - a ∣ d₁ * k := hk ▸ Nat.mul_dvd_mul_right (Nat.gcd_dvd_left d₁ d₂) k
  obtain ⟨q, hq⟩ := hdiv
  exact ⟨⟨⟨i + k * s, by rw [hs, hi, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]⟩,
      ⟨j + k * t, by rw [ht, hj, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]⟩⟩,
    ⟨q * s, by rw [hs, hq, Nat.mul_assoc]⟩⟩

end MetaMathlibExt
