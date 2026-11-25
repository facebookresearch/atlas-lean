/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.RainbowPowerDifference
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for `MathlibExt.Combinatorics.Additive.RainbowPowerDifference` -/

namespace MathlibExtTest.RainbowPowerDifference

open MetaMathlibExt

-- For the even numbers and n₀ = 3 the recurring gap must attain the upper bound 2.
example : ∀ i : ℕ, ∃ j : ℕ, i < j ∧ 2 ∣ j ∧ 2 ∣ j + 2 := by
  obtain ⟨d, hd, hd', h⟩ := exists_small_gap_of_limsup_count {x | 2 ∣ x} 3 (by decide) (by
    intro M N
    obtain ⟨m, hm⟩ := exists_nat_gt M
    let t := m + N
    refine ⟨6 * t, by dsimp [t]; omega, ?_⟩
    change M < (((Finset.Ioc 0 (6 * t)).filter (2 ∣ ·)).card : ℝ) - (6 * t : ℕ) / 3
    rw [Nat.Ioc_filter_dvd_card_eq_div, show 6 * t / 2 = 3 * t by omega]
    push_cast
    have hmt : (m : ℝ) ≤ t := by exact_mod_cast Nat.le_add_right m N
    linarith)
  obtain ⟨j, _, hj, hjd⟩ := h 0
  change 2 ∣ j at hj
  change 2 ∣ j + d at hjd
  obtain rfl : d = 2 := by omega
  exact h

-- At n₀ = 2 the even numbers realize density 1/2, but their count has no unbounded excess.
example : ¬ ∀ M : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    M < (((Finset.Icc 1 n).filter (2 ∣ ·)).card : ℝ) - n / 2 := by
  intro hdens
  obtain ⟨d, hd, hd', h⟩ :=
    exists_small_gap_of_limsup_count {x | 2 ∣ x} 2 (by decide) (by simpa using hdens)
  obtain ⟨j, _, hj, hjd⟩ := h 0
  change 2 ∣ j at hj
  change 2 ∣ j + d at hjd
  omega

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

private theorem c₇_hits (j : Fin 3) : ∃ i : ℕ, 0 < i ∧ c₇ i = j := by
  obtain ⟨a, ha⟩ := c₇_surjective j
  refine ⟨a.val + 7, by omega, ?_⟩
  simpa only [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val] using ha

private theorem c₇_nat_rainbowFree (x y z : ℕ) (_ : 0 < x) (_ : 0 < y) (_ : 0 < z)
    (h : x = y + z ^ 2) : ¬ (c₇ x ≠ c₇ y ∧ c₇ y ≠ c₇ z ∧ c₇ x ≠ c₇ z) := by
  apply c₇_rainbowFree
  simp [h]

-- Lift the coloring modulo seven to the positive integers. On [2, 7) the color changes only
-- at the last entry, where 6 has the color of 1.
example : c₇ 1 ∈ (Finset.Ico 2 7).image (fun n : ℕ => c₇ n) :=
  color_one_dominant_of_rainbowFree_powDiff 3 2 (fun n => c₇ n) c₇_hits c₇_nat_rainbowFree
    2 5 (by decide) (by decide)

-- Every block of seven contains all colors, so n₀ = 8 gives unbounded excess for all three.
-- The non-dominant run at 2, 3, 4, 5 forces the uniform bound to be at least four.
example : ∃ L : ℕ, 4 ≤ L ∧ ∀ i ℓ : ℕ, 0 < i → c₇ i ≠ c₇ 1 →
    (∀ t < ℓ, c₇ (i + t : ℕ) = c₇ i) → ℓ ≤ L := by
  have hdom := color_one_dominant_of_rainbowFree_powDiff 3 2 (fun n => c₇ n) c₇_hits
    c₇_nat_rainbowFree
  obtain ⟨L, hL⟩ := nondominant_string_length_bounded 2 (fun n => c₇ n) c₇_nat_rainbowFree
    8 (by decide) (by
      intro M N
      obtain ⟨m, hm⟩ := exists_nat_gt M
      let t := m + N
      refine ⟨56 * t, by dsimp [t]; omega, fun e => ?_⟩
      obtain ⟨a, ha⟩ := c₇_surjective e
      let r := (a - 1).val + 1
      have hr : r ≤ 7 := ZMod.val_lt (a - 1)
      have hmap : Set.MapsTo (fun j => 7 * j + r) (Finset.range (8 * t))
          ((Finset.Icc 1 (56 * t)).filter fun x : ℕ => c₇ x = e) := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        change 7 * j + r ∈ _
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp [r]; omega, by omega⟩, ?_⟩
        simpa [r, show (7 : ZMod 7) = 0 by decide] using ha
      have hcard := Finset.card_le_card_of_injOn _ hmap (by
        intro x _ y _ h
        dsimp at h
        omega)
      rw [Finset.card_range] at hcard
      have hreal := (Nat.cast_le (α := ℝ)).mpr hcard
      push_cast at hreal ⊢
      have hmt : (m : ℝ) ≤ t := by exact_mod_cast Nat.le_add_right m N
      linarith) (c₇ 1) hdom
  exact ⟨L, hL 2 4 (by decide) (by decide) (by decide), hL⟩

-- The inputs 6 and 2 share a factor, have different colors, and occur in decreasing order.
example : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ c₇ a = 1 ∧ c₇ b = 2 ∧
    ((a : ℤ) - b).natAbs = 4 :=
  exists_coprime_same_colors_of_coprime_dist 7 c₇ 6 2 (by decide) (by decide) (by decide)

-- At distance zero the representatives coincide, so coprimality forces both to be one.
example (c : ZMod 1 → Fin 3) (i : ℕ) (hi : 0 < i) : c 1 = c i := by
  obtain ⟨a, b, _, _, hcop, ha, _, hdist⟩ :=
    exists_coprime_same_colors_of_coprime_dist 1 c i i hi hi (by simp)
  obtain rfl : a = b := by omega
  have ha₁ : a = 1 := by simpa [Nat.Coprime] using hcop
  simpa only [ha₁, Nat.cast_one] using ha

-- Modulus zero allows any coloring of the integers and forces the input distance to be one.
example (c : ZMod 0 → Fin 3) (i : ℕ) (hi : 0 < i) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ c a = c i ∧ c b = c (i + 1) ∧
      ((a : ℤ) - b).natAbs = 1 := by
  simpa using
    exists_coprime_same_colors_of_coprime_dist 0 c i (i + 1) hi (by omega) (by simp)

/-- For `p = 7` and `k = 2`, every divisor of `p - 1 = 6` coprime to `k` is at most `3`, so `3` is
the largest such divisor. -/
private theorem le_three_of_dvd_six_of_coprime_two (s : ℕ) (hs : s ∣ 7 - 1)
    (hcop : Nat.Coprime s 2) : s ≤ 3 :=
  (by decide : ∀ s < 7, s ∣ 7 - 1 → Nat.Coprime s 2 → s ≤ 3) s
    (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hs)) hs hcop

-- Test section: for `p = 7` and `k = 2`, the vertex `2` lies on the cycle `2 → 4 → 2` of
-- `x ↦ x ^ 2`, so its order divides `t = 3`.
example : orderOf (2 : ZMod 7) ∣ 3 :=
  (isCycleVertex_powMap_iff_orderOf_dvd 7 2 (by decide) 3 (by decide) (by decide)
    le_three_of_dvd_six_of_coprime_two 2 (by decide)).1 ⟨2, by norm_num, by decide⟩

-- The vertex `3` has order `6`, which does not divide `3`, so no iterate `3 ^ 2 ^ m` with `m ≥ 1`
-- returns to `3` (the path is `3 → 2 → 4 → 2 → ⋯`).
example : ¬ ∃ m : ℕ, 1 ≤ m ∧ (3 : ZMod 7) ^ 2 ^ m = 3 := by
  rw [isCycleVertex_powMap_iff_orderOf_dvd 7 2 (by decide) 3 (by decide) (by decide)
    le_three_of_dvd_six_of_coprime_two 3 (by decide), orderOf_dvd_iff_pow_eq_one]
  decide

-- For `k = 1` every element is fixed and `t = p - 1`, which recovers `orderOf a ∣ p - 1`.
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) : orderOf a ∣ p - 1 :=
  (isCycleVertex_powMap_iff_orderOf_dvd p 1 hp (p - 1) dvd_rfl (Nat.coprime_one_right _)
    (fun s hs _ => Nat.le_of_dvd (by have := (Fact.out : p.Prime).two_le; omega) hs) a ha).1
    ⟨1, le_rfl, by simp⟩

-- For `k = 0` the only divisor coprime to `k` is `t = 1`, so `1` is the only nonzero cycle vertex.
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) (ha : a ≠ 0)
    (h : ∃ m : ℕ, 1 ≤ m ∧ a ^ (0 ^ m) = a) : a = 1 :=
  orderOf_eq_one_iff.1 <| Nat.dvd_one.1 <|
    (isCycleVertex_powMap_iff_orderOf_dvd p 0 hp 1 (one_dvd _) (Nat.coprime_one_left _)
      (fun s _ hs => ((Nat.coprime_zero_right s).1 hs).le) a ha).1 h

-- For coprime generators, the divisibility condition is automatic.
example : ∃ n₀ : ℕ, ∀ m : ℕ, n₀ < m → ∃ u v : ℕ, m = u * 4 + v * 7 := by
  have hg : Nat.gcd 4 7 = 1 := by decide
  simpa only [hg, one_dvd, true_implies] using
    exists_forall_gcd_dvd_eq_add_mul 4 7 (by decide) (by decide)

-- With gcd 2, the conclusion covers all sufficiently large even numbers.
example : ∃ n₀ : ℕ, ∀ m : ℕ, n₀ < m → 2 ∣ m → ∃ u v : ℕ, m = u * 6 + v * 10 := by
  have hg : Nat.gcd 6 10 = 2 := by decide
  simpa only [hg] using exists_forall_gcd_dvd_eq_add_mul 6 10 (by decide) (by decide)

-- A generator equal to 1 is allowed.
example : ∃ n₀ : ℕ, ∀ m : ℕ, n₀ < m → ∃ u v : ℕ, m = u * 9 + v := by
  simpa only [Nat.gcd_one_right, one_dvd, true_implies, mul_one] using
    exists_forall_gcd_dvd_eq_add_mul 9 1 (by decide) (by decide)

-- The solution 15 = 6 + 3² reduces to 1 - 6 = 3² modulo seven.
example : ¬ (c₇ 1 ≠ c₇ 6 ∧ c₇ 6 ≠ c₇ 3 ∧ c₇ 1 ≠ c₇ 3) :=
  rainbowFree_powDiff_lift_of_zmod 7 2 c₇ c₇_rainbowFree 15 6 3
    (by decide) (by decide) (by decide) (by decide)

-- At modulus zero the coloring has domain ℤ. Exponent zero gives consecutive inputs.
example (c : ℤ → Fin 3)
    (hrf : ∀ x y z : ℤ, x - y = 1 → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)) :
    ¬ (c 6 ≠ c 5 ∧ c 5 ≠ c 2 ∧ c 6 ≠ c 2) :=
  rainbowFree_powDiff_lift_of_zmod 0 0 c
    (fun x y z h => hrf x y z (h.trans (pow_zero z))) 6 5 2
    (by decide) (by decide) (by decide) (by decide)

end MathlibExtTest.RainbowPowerDifference
