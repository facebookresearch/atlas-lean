/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniqueness

/-!
# Nonagonal additive uniqueness: the step at powers of 7

A multiplicative arithmetic function additive on pairs of positive generalized nonagonal
numbers takes the value `7 ^ r` at `7 ^ r` whenever it is the identity below `7 ^ r`.

Statements from Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99. The generalized nonagonal numbers
are the values `m (7m - 5) / 2` for `m ∈ ℤ` (`0, 1, 6, 9, 19, 24, 39, …`, OEIS A118277),
written below without division as `2a = m (7m - 5)`. Multiplicative functions are
`ArithmeticFunction ℂ` with `IsMultiplicative`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

namespace multiplicative_nonagonal_additive_seven_pow

private def poly (m : ℤ) : ℤ := m * (7 * m - 5)

private def nonagon (m : ℤ) : ℕ := (poly m / 2).toNat

private lemma twice_nonagon (m : ℤ) : 2 * (nonagon m : ℤ) = poly m := by
  have h : 0 ≤ poly m := by
    by_cases hm : m ≤ 0
    · exact mul_nonneg_of_nonpos_of_nonpos hm (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have hmod : poly m % 2 = 0 := by
    rw [poly, Int.mul_emod, Int.sub_emod, Int.mul_emod 7 m]
    rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with H | H <;> simp [H]
  unfold nonagon
  omega

private abbrev Additive (f : ArithmeticFunction ℂ) :=
  ∀ a b : ℕ, 0 < a → 0 < b →
    (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
      f (a + b) = f a + f b

private lemma add_nonagon {f : ArithmeticFunction ℂ} (hadd : Additive f) (m k : ℤ) :
    f (nonagon m + nonagon k) = f (nonagon m) + f (nonagon k) := by
  rcases Nat.eq_zero_or_pos (nonagon m) with hm | hm
  · simp [hm]
  rcases Nat.eq_zero_or_pos (nonagon k) with hk | hk
  · simp [hk]
  exact hadd _ _ hm hk ⟨m, twice_nonagon m⟩ ⟨k, twice_nonagon k⟩

private abbrev Reduces (m k a b : ℤ) : Prop :=
  poly m + poly k = poly a + poly b ∧
    (14 * k - 5).natAbs < (14 * m - 5).natAbs ∧ (14 * a - 5).natAbs < (14 * m - 5).natAbs ∧
    (14 * b - 5).natAbs < (14 * m - 5).natAbs

-- Rotate the pair (14m - 5, 14k - 5) by a rational orthogonal matrix with
-- entries -24/25 and ±7/25. The congruence on k makes both new indices integral.
private lemma rotate (m : ℤ) (hm : m < -35 ∨ 35 < m) : ∃ k a b, Reduces m k a b := by
  let k := if 0 < m then -((7 * m + 15) % 25) else (-7 * m - 15) % 25
  let a := (-24 * m - 7 * k + 20) / 25
  let b := (7 * m - 24 * k + 15) / 25
  have ha : 25 * a = -24 * m - 7 * k + 20 := by dsimp [a, k]; split <;> omega
  have hb : 25 * b = 7 * m - 24 * k + 15 := by dsimp [b, k]; split <;> omega
  refine ⟨k, a, b, ?_, ?_, ?_, ?_⟩
  · have h : 625 * (poly a + poly b) = 625 * (poly m + poly k) := calc
        _ = 7 * (25 * a) ^ 2 - 125 * (25 * a) + 7 * (25 * b) ^ 2 - 125 * (25 * b) := by
          unfold poly
          ring
        _ = _ := by rw [ha, hb]; unfold poly; ring
    omega
  all_goals
    dsimp [k] at *
    split at * <;> omega

private abbrev Exceptional (m : ℤ) : Prop :=
  m = 0 ∨ m = 1 ∨ m = -1 ∨ m = 2 ∨ m = -2 ∨ m = 4 ∨ m = -5 ∨ m = -7

-- On the interval from -35 to 35, try both orientations of the rotation
-- and the six additional equal sums below.
private def smallSplits (m : ℤ) : List (ℤ × ℤ × ℤ) :=
  let k := (-7 * m - 15) % 25
  let l := (7 * m - 20) % 25
  ([k, k - 25].map fun t ↦ (t, (-24 * m - 7 * t + 20) / 25, (7 * m - 24 * t + 15) / 25)) ++
    ([l, l - 25].map fun t ↦ (t, (-24 * m + 7 * t + 15) / 25, (-7 * m - 24 * t + 20) / 25)) ++
    [(2, 3, 3), (-2, 4, -3), (-3, 5, 5), (2, 3, -7), (-4, 9, 6), (-7, 11, -8)]

private lemma reduction (m : ℤ) (hm : ¬ Exceptional m) : ∃ k a b, Reduces m k a b := by
  by_cases h : m < -35 ∨ 35 < m
  · exact rotate m h
  have finite : ∀ i : Fin 71, let j := (i : ℤ) - 35
      Exceptional j ∨ ∃ w ∈ smallSplits j, Reduces j w.1 w.2.1 w.2.2 := by decide
  let i : Fin 71 := ⟨(m + 35).toNat, by omega⟩
  have hi : (i : ℤ) - 35 = m := by dsimp [i]; omega
  have H := finite i
  dsimp only at H
  rw [hi] at H
  obtain ⟨w, _, hw⟩ := H.resolve_left hm
  exact ⟨_, _, _, hw⟩

private lemma fixed_exceptional {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (hadd : Additive f) (m : ℤ) (hm : Exceptional m) : f (nonagon m) = nonagon m := by
  have small := multiplicative_nonagonal_additive_eq_self_of_le_eleven f hf hadd
  have mul (a b : ℕ) (h : a.Coprime b) (ha : f a = a) (hb : f b = b) :
      f (a * b) = (a * b : ℕ) := by rw [hf.map_mul_of_coprime h, ha, hb, Nat.cast_mul]
  have h1 := small 1 (by decide) (by decide)
  have h4 := small 4 (by decide) (by decide)
  have h5 := small 5 (by decide) (by decide)
  have h9 := small 9 (by decide) (by decide)
  have h11 := small 11 (by decide) (by decide)
  have h20 := mul 4 5 (by decide) h4 h5
  have h55 := mul 5 11 (by decide) h5 h11
  have h24 := mul 3 8 (by decide)
    (small _ (by decide) (by decide)) (small _ (by decide) (by decide))
  have h25 : f 25 = 25 := by
    linear_combination (norm := (norm_num [nonagon, poly]; ring)) add_nonagon hadd 3 1 + h24 + h1
  have h100 := mul 4 25 (by decide) h4 (by exact_mod_cast h25)
  have h198 := mul 2 99 (by decide) (small _ (by decide) (by decide))
    (mul 9 11 (by decide) h9 h11)
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [nonagon, poly]
  · exact h1
  · exact small 6 (by decide) (by decide)
  · exact h9
  · linear_combination (norm := (norm_num [nonagon, poly]; ring))
      h20 - add_nonagon hadd (-2) 1 - h1
  · linear_combination (norm := (norm_num [nonagon, poly]; ring))
      h55 - add_nonagon hadd 4 2 - h9
  · exact h100
  · linear_combination (norm := (norm_num [nonagon, poly]; ring))
      h198 - add_nonagon hadd (-7) 2 - h9

private lemma fixed_nonagon {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (hadd : Additive f) (m : ℤ) : f (nonagon m) = nonagon m := by
  generalize ht : (14 * m - 5).natAbs = t
  induction t using Nat.strong_induction_on generalizing m with
  | ind t ih =>
    by_cases hm : Exceptional m
    · exact fixed_exceptional hf hadd m hm
    obtain ⟨k, a, b, heq, hk, ha, hb⟩ := reduction m hm
    have hsum : nonagon m + nonagon k = nonagon a + nonagon b := by
      have := twice_nonagon m
      have := twice_nonagon k
      have := twice_nonagon a
      have := twice_nonagon b
      omega
    have H := add_nonagon hadd m k
    rw [hsum, add_nonagon hadd, ih _ (ht ▸ ha) a rfl, ih _ (ht ▸ hb) b rfl,
      ih _ (ht ▸ hk) k rfl, ← Nat.cast_add, ← hsum, Nat.cast_add] at H
    exact add_right_cancel H.symm

-- A representation of the product nq as a sum of two generalized nonagonal numbers.
private def Represents (n q : ℕ) (a b : ℤ) : Prop :=
  poly a + poly b = 2 * (n : ℤ) * q

private lemma fixed_of_represents {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (hadd : Additive f) {n q : ℕ} (hq : 0 < q) (hc : n.Coprime q) (hfix : f q = q)
    {a b : ℤ} (h : Represents n q a b) : f n = n := by
  have hsum : nonagon a + nonagon b = n * q := by
    unfold Represents at h
    have := twice_nonagon a
    have := twice_nonagon b
    zify
    linarith
  have H := add_nonagon hadd a b
  rw [hsum, hf.map_mul_of_coprime hc, hfix, fixed_nonagon hf hadd a, fixed_nonagon hf hadd b,
    ← Nat.cast_add, hsum, Nat.cast_mul] at H
  exact mul_right_cancel₀ (by exact_mod_cast hq.ne') H

private def Smaller (n q : ℕ) : Prop := 0 < q ∧ q < n ∧ ∃ a b, Represents n q a b

-- For a power of 7, work modulo 10. In each row the cofactor is nonzero modulo 7.
private lemma seven_representations (t u : ℕ) (hu : u = 1 ∨ u = 3 ∨ u = 7 ∨ u = 9)
    (hn : 11 < 10 * t + u) : ∃ q, Smaller (10 * t + u) q ∧ ¬ 7 ∣ q := by
  rcases hu with rfl | rfl | rfl | rfl
  · refine ⟨7 * t + 2, ⟨?_, ?_, 4 * (t : ℤ) + 1, 2 * (t : ℤ) + 1, ?_⟩, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring
  · refine ⟨7 * t + 3, ⟨?_, ?_, -2 * (t : ℤ), 4 * (t : ℤ) + 2, ?_⟩, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring
  · refine ⟨7 * t + 4, ⟨?_, ?_, 2 * (t : ℤ) + 2, -4 * (t : ℤ) - 2, ?_⟩, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring
  · refine ⟨7 * t + 5, ⟨?_, ?_, -4 * (t : ℤ) - 3, -2 * (t : ℤ) - 1, ?_⟩, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring

end multiplicative_nonagonal_additive_seven_pow

open multiplicative_nonagonal_additive_seven_pow

/-- **Nonagonal additive uniqueness: the step at powers of 7.** Let $f$ be a multiplicative
arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$ for all
positive integers $a$ and $b$ that are generalized nonagonal numbers, that is, $2a = m(7m - 5)$
and $2b = k(7k - 5)$ for some integers $m$ and $k$. Let $r$ be a natural number. If $f(n) = n$
for every natural number $n < 7^r$, then $f(7^r) = 7^r$.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 4
(`integers-2025-A99-thm-4`). -/
public theorem multiplicative_nonagonal_additive_seven_pow
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) (r : ℕ)
    (hind : ∀ n : ℕ, n < 7 ^ r → f n = n) :
    f (7 ^ r) = (7 ^ r : ℕ) := by
  by_cases hsmall : 7 ^ r ≤ 11
  · exact multiplicative_nonagonal_additive_eq_self_of_le_eleven f hf hadd _
      (Nat.one_le_pow r 7 (by decide)) hsmall
  · have hlt : 11 < 7 ^ r := by omega
    have h2 : ¬ 2 ∣ 7 ^ r := fun hd ↦ absurd (Nat.prime_two.dvd_of_dvd_pow hd) (by decide)
    have h5 : ¬ 5 ∣ 7 ^ r :=
      fun hd ↦ absurd ((by decide : Nat.Prime 5).dvd_of_dvd_pow hd) (by decide)
    let t := 7 ^ r / 10
    let u := 7 ^ r % 10
    have he : 10 * t + u = 7 ^ r := by dsimp [t, u]; omega
    have hu : u = 1 ∨ u = 3 ∨ u = 7 ∨ u = 9 := by dsimp [u]; omega
    obtain ⟨q, hs, hq⟩ := seven_representations t u hu (he ▸ hlt)
    have hs' : Smaller (7 ^ r) q := he ▸ hs
    obtain ⟨hqpos, hqlt, a, b, hr⟩ := hs'
    have hc : Nat.Coprime (7 ^ r) q :=
      ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr hq).pow_left r
    exact fixed_of_represents hf hadd hqpos hc (hind q hqlt) hr

end MetaMathlibExt
