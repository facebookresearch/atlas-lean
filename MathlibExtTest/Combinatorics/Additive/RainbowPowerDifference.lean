/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.RainbowPowerDifference
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for `MathlibExt.Combinatorics.Additive.RainbowPowerDifference` -/

namespace MathlibExtTest.RainbowPowerDifference

open MetaMathlibExt

private instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The exact 3-coloring of `ℤ/7ℤ` with color classes `{0}`, `{±1}` and `{±2, ±3}`. -/
private def c₇ : ZMod 7 → Fin 3 := fun x => if x = 0 then 0 else if x = 1 ∨ x = -1 then 1 else 2

-- Test section: `c₇` is exact and rainbow-free for `x - y = z ^ 2` (the squares mod `7` are
-- `0, 1, 2, 4`), so the hypotheses of the theorem are satisfiable.
private theorem c₇_surjective : Function.Surjective c₇ := by decide

private theorem c₇_rainbowFree :
    ∀ x y z : ZMod 7, x - y = z ^ 2 → ¬ (c₇ x ≠ c₇ y ∧ c₇ y ≠ c₇ z ∧ c₇ x ≠ c₇ z) := by
  decide

-- Test section: for `a = 3` we have `a ^ 2 = 2`, and the `2`-string at `1` of length `3` is
-- `2, 4, 6`, with colors `2, 2, 1`. It is bichromatic, so it contains `c₇ 3 = 2`.
example : c₇ 3 ∈ (Finset.range 3).image fun t : ℕ => c₇ ((1 + t) * 3 ^ 2) :=
  color_dominant_powStrings_of_rainbowFree_zmod 7 2 c₇ c₇_surjective c₇_rainbowFree 3
    (by decide) 1 3 (by decide)

-- Test section: strings of length two. If `i aᵏ` and `(i + 1) aᵏ` have different colors, one of
-- them has the color `c a`.
example (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) (ha : a ≠ 0) (i : ZMod p) (hne : c (i * a ^ k) ≠ c ((i + 1) * a ^ k)) :
    c a = c (i * a ^ k) ∨ c a = c ((i + 1) * a ^ k) := by
  have hbi : ((Finset.range 2).image fun t : ℕ => c ((i + t) * a ^ k)).card = 2 := by
    simpa [Finset.range_add_one, Finset.image_insert] using Finset.card_pair hne.symm
  simpa [Finset.range_add_one, Finset.image_insert, or_comm] using
    color_dominant_powStrings_of_rainbowFree_zmod p k c hc hrf a ha i 2 hbi

/-- The exact 3-coloring of `ℤ/7ℤ` with color classes `{3}`, `{0}` and `{1, 2, 4, 5, 6}`. -/
private def d₇ : ZMod 7 → Fin 3 := fun x => if x = 3 then 0 else if x = 0 then 1 else 2

-- Test section: rainbow-freeness is needed. The `2`-string `0, 2` (`3 ^ 2 = 2`) of the exact
-- coloring `d₇` is bichromatic and misses the color of `3`, so the theorem shows that `d₇` has a
-- rainbow solution of `x - y = z ^ 2` (for instance `(2, 0, 3)`).
example : ¬ ∀ x y z : ZMod 7, x - y = z ^ 2 → ¬ (d₇ x ≠ d₇ y ∧ d₇ y ≠ d₇ z ∧ d₇ x ≠ d₇ z) := by
  intro hrf
  have hmem := color_dominant_powStrings_of_rainbowFree_zmod 7 2 d₇ (by decide) hrf 3
    (by decide) 0 2 (by decide)
  revert hmem
  decide

end MathlibExtTest.RainbowPowerDifference
