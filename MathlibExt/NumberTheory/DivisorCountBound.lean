/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Divisors

/-!
# A square-root bound for the divisor count

In each factor pair of a positive integer `n`, the smaller factor lies in `[1, Nat.sqrt n]`.
Each integer in this interval accounts for at most two divisors.
-/

namespace MetaMathlibExt

/-- **Square-root bound for the number of divisors.** For every natural number $n$, the number
of positive divisors of $n$ is at most $2\sqrt{n}$. For $n = 0$ the set of divisors is taken to
be empty, so the bound holds trivially.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 12 (`jis-2024-24.2.5-lem-12`). -/
public theorem card_divisors_le_two_mul_sqrt (n : ℕ) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt n := by
  let small := Finset.Icc 1 n.sqrt
  have hcover : n.divisors ⊆ small ∪ small.image (n / ·) := by
    intro d hd
    obtain ⟨hdvd, hn⟩ := Nat.mem_divisors.mp hd
    have hdpos := Nat.pos_of_mem_divisors hd
    rcases Nat.le_sqrt_of_eq_mul (Nat.div_mul_cancel hdvd).symm with hq | hs
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨n / d, Finset.mem_Icc.mpr
        ⟨Nat.div_pos (Nat.divisor_le hd) hdpos, hq⟩, Nat.div_div_self hdvd hn⟩
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hdpos, hs⟩)
  have hcard : n.divisors.card ≤ 2 * n.sqrt := calc
    n.divisors.card ≤ (small ∪ small.image (n / ·)).card := Finset.card_le_card hcover
    _ ≤ small.card + (small.image (n / ·)).card := Finset.card_union_le _ _
    _ ≤ small.card + small.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * n.sqrt := by simp [small, two_mul]
  calc
    (n.divisors.card : ℝ) ≤ 2 * (n.sqrt : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * Real.sqrt n := mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)

end MetaMathlibExt
