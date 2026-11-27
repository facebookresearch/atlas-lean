/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vieta jumping preserves induced solutions of the generalized second Markov equation

This module defines induced solutions of the generalized second Markov equation and proves
that Vieta jumping preserves them.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.7.
-/

namespace MetaMathlibExt

/-- **Induced solution of the generalized second Markov equation.** For a natural number $k$,
a triple $(a, b, c)$ of integers is an induced positive solution of the $k$-generalized second
Markov equation $\mathrm{GSME}(k)$ when $a, b, c > 0$,
$$a^2 + b^2 + c^2 + (k^2 + 2k)(a + b + c) + 2k^3 + 3k^2 = abc,$$
and $3 + 3k$ divides each of $a + k$, $b + k$ and $c + k$.

Equivalently, $(a + k)/(3 + 3k)$, $(b + k)/(3 + 3k)$ and $(c + k)/(3 + 3k)$ are integers; they
are automatically positive since $a, b, c > 0$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
@[expose] public def IsInducedGenSecondMarkovSolution (k : ℕ) (a b c : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
    a ^ 2 + b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + b + c) + 2 * (k : ℤ) ^ 3 +
      3 * (k : ℤ) ^ 2 = a * b * c ∧
    (3 + 3 * (k : ℤ)) ∣ a + k ∧ (3 + 3 * (k : ℤ)) ∣ b + k ∧ (3 + 3 * (k : ℤ)) ∣ c + k

/-- **Vieta jumping preserves induced solutions of the generalized second Markov equation.** If
$(a, b, c)$ is an induced solution of the $k$-generalized second Markov equation
$\mathrm{GSME}(k)$, then so are $(a, ab - c - k^2 - 2k, b)$ and $(b, bc - a - k^2 - 2k, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.7. -/
public theorem IsInducedGenSecondMarkovSolution.vieta {k : ℕ} {a b c : ℤ}
    (h : IsInducedGenSecondMarkovSolution k a b c) :
    IsInducedGenSecondMarkovSolution k a (a * b - c - (k : ℤ) ^ 2 - 2 * k) b ∧
      IsInducedGenSecondMarkovSolution k b (b * c - a - (k : ℤ) ^ 2 - 2 * k) c := by
  obtain ⟨ha, hb, hc, heq, hda, hdb, hdc⟩ := h
  have hprod_c : c * (a * b - c - (k : ℤ) ^ 2 - 2 * (k : ℤ)) =
      a ^ 2 + b ^ 2 + ((k : ℤ) ^ 2 + 2 * (k : ℤ)) * (a + b) + 2 * (k : ℤ) ^ 3 +
        3 * (k : ℤ) ^ 2 := by linear_combination -heq
  have hprod_a : a * (b * c - a - (k : ℤ) ^ 2 - 2 * (k : ℤ)) =
      b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * (k : ℤ)) * (b + c) + 2 * (k : ℤ) ^ 3 +
        3 * (k : ℤ) ^ 2 := by linear_combination -heq
  have hpos_c : 0 < a ^ 2 + b ^ 2 + ((k : ℤ) ^ 2 + 2 * (k : ℤ)) * (a + b) +
      2 * (k : ℤ) ^ 3 + 3 * (k : ℤ) ^ 2 := by positivity
  have hpos_a : 0 < b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * (k : ℤ)) * (b + c) +
      2 * (k : ℤ) ^ 3 + 3 * (k : ℤ) ^ 2 := by positivity
  have hcc : 0 < c * (a * b - c - (k : ℤ) ^ 2 - 2 * (k : ℤ)) := by
    rw [hprod_c]
    exact hpos_c
  have haa : 0 < a * (b * c - a - (k : ℤ) ^ 2 - 2 * (k : ℤ)) := by
    rw [hprod_a]
    exact hpos_a
  have hc'_pos : 0 < a * b - c - (k : ℤ) ^ 2 - 2 * (k : ℤ) :=
    pos_of_mul_pos_right hcc (le_of_lt hc)
  have ha'_pos : 0 < b * c - a - (k : ℤ) ^ 2 - 2 * (k : ℤ) :=
    pos_of_mul_pos_right haa (le_of_lt ha)
  have heq1 : a ^ 2 + (a * b - c - (k : ℤ) ^ 2 - 2 * (k : ℤ)) ^ 2 + b ^ 2 +
      ((k : ℤ) ^ 2 + 2 * (k : ℤ)) * (a + (a * b - c - (k : ℤ) ^ 2 - 2 * (k : ℤ)) + b) +
      2 * (k : ℤ) ^ 3 + 3 * (k : ℤ) ^ 2 =
      a * (a * b - c - (k : ℤ) ^ 2 - 2 * (k : ℤ)) * b := by linear_combination heq
  have heq2 : b ^ 2 + (b * c - a - (k : ℤ) ^ 2 - 2 * (k : ℤ)) ^ 2 + c ^ 2 +
      ((k : ℤ) ^ 2 + 2 * (k : ℤ)) * (b + (b * c - a - (k : ℤ) ^ 2 - 2 * (k : ℤ)) + c) +
      2 * (k : ℤ) ^ 3 + 3 * (k : ℤ) ^ 2 =
      b * (b * c - a - (k : ℤ) ^ 2 - 2 * (k : ℤ)) * c := by linear_combination heq
  have hdvd1 : (3 + 3 * (k : ℤ)) ∣ (a * b - c - (k : ℤ) ^ 2 - 2 * (k : ℤ)) + (k : ℤ) := by
    have he : (a * b - c - (k : ℤ) ^ 2 - 2 * (k : ℤ)) + (k : ℤ) =
        (a + (k : ℤ)) * (b + (k : ℤ)) - (k : ℤ) * (a + (k : ℤ)) -
          (k : ℤ) * (b + (k : ℤ)) - (c + (k : ℤ)) := by ring
    rw [he]
    exact dvd_sub (dvd_sub (dvd_sub (dvd_mul_of_dvd_left hda _)
      (dvd_mul_of_dvd_right hda _)) (dvd_mul_of_dvd_right hdb _)) hdc
  have hdvd2 : (3 + 3 * (k : ℤ)) ∣ (b * c - a - (k : ℤ) ^ 2 - 2 * (k : ℤ)) + (k : ℤ) := by
    have he : (b * c - a - (k : ℤ) ^ 2 - 2 * (k : ℤ)) + (k : ℤ) =
        (b + (k : ℤ)) * (c + (k : ℤ)) - (k : ℤ) * (b + (k : ℤ)) -
          (k : ℤ) * (c + (k : ℤ)) - (a + (k : ℤ)) := by ring
    rw [he]
    exact dvd_sub (dvd_sub (dvd_sub (dvd_mul_of_dvd_left hdb _)
      (dvd_mul_of_dvd_right hdb _)) (dvd_mul_of_dvd_right hdc _)) hda
  exact ⟨⟨ha, hc'_pos, hb, heq1, hda, hdvd1, hdb⟩,
    ⟨hb, ha'_pos, hc, heq2, hdb, hdvd2, hdc⟩⟩

end MetaMathlibExt
