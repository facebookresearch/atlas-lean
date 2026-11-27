/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

/-!
# Additive uniqueness of generalized nonagonal numbers

A complex-valued multiplicative arithmetic function additive on pairs of positive generalized
nonagonal numbers fixes every natural number. Two decompositions each of 90 and 94 give the
initial values. Equal sums of nonagonal numbers then determine the function on all nonagonal
numbers by induction on the absolute value of the shifted index `14m - 5`. Representations of
coprime multiples of prime powers as such sums extend the identity to all natural numbers.

## References

* Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
  Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Lemma 1 and Theorems 1 and 5.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- A multiplicative arithmetic function additive on pairs of positive generalized nonagonal
numbers fixes every integer from 1 through 11.

The ATLAS article *Nonagonal additive uniqueness: the values up to 11* attributes this result to
Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for Multiplicative
Functions*, INTEGERS 25 (2025), Article A99, Lemma 1.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Lemma 1
(`integers-2025-A99-lem-1`). -/
public theorem multiplicative_nonagonal_additive_eq_self_of_le_eleven
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 11 → f n = n := by
  let N (a : ℕ) := 0 < a ∧ ∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)
  have add {a b : ℕ} (ha : N a) (hb : N b) : f (a + b) = f a + f b :=
    hadd a b ha.1 hb.1 ha.2 hb.2
  have n1 : N 1 := ⟨by decide, 1, by decide⟩
  have n6 : N 6 := ⟨by decide, -1, by decide⟩
  have n9 : N 9 := ⟨by decide, 2, by decide⟩
  have n19 : N 19 := ⟨by decide, -2, by decide⟩
  have n24 : N 24 := ⟨by decide, 3, by decide⟩
  have n39 : N 39 := ⟨by decide, -3, by decide⟩
  have n46 : N 46 := ⟨by decide, 4, by decide⟩
  have n66 : N 66 := ⟨by decide, -4, by decide⟩
  have n75 : N 75 := ⟨by decide, 5, by decide⟩
  have h1 := hf.map_one
  have h2 : f 2 = 2 := by linear_combination add n1 n1 + 2 * h1
  have double (a : ℕ) (ha : Nat.Coprime 2 a) : f (2 * a) = 2 * f a := by
    rw [hf.map_mul_of_coprime ha, h2]
  -- Express the summands in terms of f 6 and f 9 by comparing representations of
  -- 30, 25, 48 and 66, respectively.
  have h24 : f 24 = f 6 + 2 * f 9 := by
    linear_combination double 15 (by decide) + 2 * add n6 n9 - add n6 n24
  have h19 : f 19 = 1 + 2 * f 9 := by
    linear_combination add n1 n24 - add n6 n19 + h1 + h24
  have h39 : f 39 = 2 * f 6 + 3 * f 9 := by
    linear_combination add n24 n24 - add n9 n39 + 2 * h24
  have h66 : f 66 = 2 * f 6 + 6 * f 9 := by
    linear_combination double 33 (by decide) + 2 * add n9 n24 + 2 * h24
  -- 90 = 24 + 66 = 2(6 + 39) gives the first linear relation.
  have rel90 : 3 * f 6 = 2 * f 9 := by
    linear_combination add n24 n66 - double 45 (by decide) - 2 * add n6 n39 +
      h24 + h66 - 2 * h39
  -- 85 = 19 + 66 = 39 + 46 and 75 = 9 + 66 supply the summands for the second.
  have h46 : f 46 = 1 + 5 * f 9 := by
    linear_combination add n19 n66 - add n39 n46 + h19 + h66 - h39
  have h75 : f 75 = 2 * f 6 + 7 * f 9 := by
    linear_combination add n9 n66 + h66
  -- 94 = 19 + 75 = 2(1 + 46).
  have rel94 : 2 * f 6 = 3 + f 9 := by
    linear_combination double 47 (by decide) + 2 * add n1 n46 - add n19 n75 -
      h19 - h75 + 2 * h1 + 2 * h46
  have h6 : f 6 = 6 := by linear_combination 2 * rel94 - rel90
  have h9 : f 9 = 9 := by linear_combination 3 * rel94 - 2 * rel90
  -- Recover the other values from nonagonal sums and coprime products.
  have h3 : f 3 = 3 := by linear_combination (h6 - double 3 (by decide)) / 2
  have triple (a : ℕ) (ha : Nat.Coprime 3 a) : f (3 * a) = 3 * f a := by
    rw [hf.map_mul_of_coprime ha, h3]
  have h4 : f 4 = 4 := by
    linear_combination (add n6 n6 + 2 * h6 - triple 4 (by decide)) / 3
  have h10 : f 10 = 10 := by linear_combination add n1 n9 + h1 + h9
  have h5 : f 5 = 5 := by linear_combination (h10 - double 5 (by decide)) / 2
  have h7 : f 7 = 7 := by linear_combination add n1 n6 + h1 + h6
  norm_num [h6, h9] at h24
  have h8 : f 8 = 8 := by linear_combination (h24 - triple 8 (by decide)) / 3
  have h11 : f 11 = 11 := by
    linear_combination (add n9 n24 + h9 + h24 - triple 11 (by decide)) / 3
  intro n hn hle
  interval_cases n <;> norm_num1 <;> assumption

namespace multiplicative_nonagonal_additive_eq_id

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

-- For n odd and prime to 7, the two cofactors have an integer linear combination equal to 2.
-- For instance, for n = 14t + 1 the pairs (2t, -4t) and (-4t, 2t + 1) give
-- the consecutive cofactors 5t and 5t + 1.
private lemma odd_representations (t u : ℕ)
    (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 9 ∨ u = 11 ∨ u = 13) (hn : 11 < 14 * t + u) :
    ∃ q s, Smaller (14 * t + u) q ∧ Smaller (14 * t + u) s ∧ ∃ y z : ℤ, y * q + z * s = 2 := by
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨5 * t, 5 * t + 1, ⟨?_, ?_, 2 * (t : ℤ), -4 * (t : ℤ), ?_⟩,
      ⟨?_, ?_, -4 * (t : ℤ), 2 * (t : ℤ) + 1, ?_⟩, -2, 2, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring
  · refine ⟨5 * t, 5 * t + 2, ⟨?_, ?_, -2 * (t : ℤ), -4 * (t : ℤ), ?_⟩,
      ⟨?_, ?_, -4 * (t : ℤ) - 1, -2 * (t : ℤ), ?_⟩, -1, 1, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring
  · refine ⟨t, 10 * t + 2, ⟨?_, ?_, 0, -2 * (t : ℤ), ?_⟩,
      ⟨?_, ?_, 6 * (t : ℤ) + 2, 2 * (t : ℤ) + 1, ?_⟩, -10, 1, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring
  · refine ⟨t + 1, 10 * t + 8, ⟨?_, ?_, 0, 2 * (t : ℤ) + 2, ?_⟩,
      ⟨?_, ?_, -6 * (t : ℤ) - 4, -2 * (t : ℤ) - 1, ?_⟩, 10, -1, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring
  · refine ⟨5 * t + 3, 5 * t + 5, ⟨?_, ?_, 4 * (t : ℤ) + 3, 2 * (t : ℤ) + 2, ?_⟩,
      ⟨?_, ?_, 2 * (t : ℤ) + 2, 4 * (t : ℤ) + 4, ?_⟩, -1, 1, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring
  · refine ⟨5 * t + 5, 5 * t + 4, ⟨?_, ?_, -2 * (t : ℤ) - 2, 4 * (t : ℤ) + 4, ?_⟩,
      ⟨?_, ?_, 4 * (t : ℤ) + 4, -2 * (t : ℤ) - 1, ?_⟩, 2, -2, ?_⟩ <;>
      first | omega | unfold Represents poly; push_cast; ring

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

private lemma two_residues (r : ℕ) :
    2 ^ r % 7 = 1 ∨ 2 ^ r % 7 = 2 ∨ 2 ^ r % 7 = 4 := by
  induction r with
  | zero => decide
  | succ r ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h | h <;> simp [h]

private lemma fixed_two_power {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (hadd : Additive f) {n r : ℕ} (hn : n = 2 ^ r) (hlt : 11 < n)
    (ih : ∀ q < n, f q = q) : f n = n := by
  have hc {q : ℕ} (h : ¬ 2 ∣ q) : n.Coprime q :=
    hn ▸ (Nat.prime_two.coprime_iff_not_dvd.mpr h).pow_left r
  have heven : 2 ∣ n := hn ▸ dvd_pow_self _ (by rintro rfl; simp_all)
  let t := n / 7
  have hr : n = 7 * t + 1 ∨ n = 7 * t + 2 ∨ n = 7 * t + 4 := by
    have := hn ▸ two_residues r
    dsimp [t]
    omega
  -- Factor the nonagonal number at 2t + 1, or twice the one at t + 1 or -3t - 1.
  rcases hr with h | h | h
  · apply fixed_of_represents hf hadd (q := 2 * t + 1) (a := 0) (b := 2 * (t : ℤ) + 1)
      (by omega) (hc (by omega)) (ih _ (by omega))
    unfold Represents poly
    rw [h]
    push_cast
    ring
  · apply fixed_of_represents hf hadd (q := t + 1) (a := (t : ℤ) + 1) (b := (t : ℤ) + 1)
      (by omega) (hc (by omega)) (ih _ (by omega))
    unfold Represents poly
    rw [h]
    push_cast
    ring
  · -- Here the cofactor can exceed n, but its coprime factors 3 and 3t + 1 are smaller.
    have h3 : f (3 * (3 * t + 1)) = (3 * (3 * t + 1) : ℕ) := by
      have cop : Nat.Coprime 3 (3 * t + 1) := Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
      rw [hf.map_mul_of_coprime cop, ih 3 (by omega), ih (3 * t + 1) (by omega), Nat.cast_mul]
    apply fixed_of_represents hf hadd (by omega) (hc (by omega)) h3
      (a := -3 * (t : ℤ) - 1) (b := -3 * (t : ℤ) - 1)
    unfold Represents poly
    rw [h]
    push_cast
    ring

private lemma fixed_prime_power {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
    (hadd : Additive f) {p r n : ℕ} (hp : p.Prime) (hn : n = p ^ r) (hlt : 11 < n)
    (ih : ∀ q < n, f q = q) : f n = n := by
  rcases eq_or_ne p 2 with rfl | hp2
  · exact fixed_two_power hf hadd hn hlt ih
  have cancel {q : ℕ} (hs : Smaller n q) (h : ¬ p ∣ q) : f n = n := by
    obtain ⟨hq, hlt, a, b, hr⟩ := hs
    have hc : n.Coprime q := hn ▸ (hp.coprime_iff_not_dvd.mpr h).pow_left r
    exact fixed_of_represents hf hadd hq hc (ih _ hlt) hr
  have avoid {k : ℕ} (hk : k.Prime) (h : p ≠ k) : ¬ k ∣ n := by
    rw [hn]
    exact fun hd ↦ h ((Nat.prime_dvd_prime_iff_eq hk hp).mp (hk.dvd_of_dvd_pow hd)).symm
  have hodd := avoid Nat.prime_two hp2
  rcases eq_or_ne p 7 with rfl | hp7
  · have h5 := avoid (by decide : Nat.Prime 5) (by decide)
    let t := n / 10
    let u := n % 10
    have he : 10 * t + u = n := by dsimp [t, u]; omega
    have hu : u = 1 ∨ u = 3 ∨ u = 7 ∨ u = 9 := by dsimp [u]; omega
    obtain ⟨q, hs, hq⟩ := seven_representations t u hu (he ▸ hlt)
    exact cancel (he ▸ hs) hq
  · have h7 := avoid (by decide : Nat.Prime 7) hp7
    let t := n / 14
    let u := n % 14
    have he : 14 * t + u = n := by dsimp [t, u]; omega
    have hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 9 ∨ u = 11 ∨ u = 13 := by dsimp [u]; omega
    obtain ⟨q, s, hq, hs, y, z, hbez⟩ := odd_representations t u hu (he ▸ hlt)
    by_cases hd : p ∣ q
    · apply cancel (he ▸ hs)
      intro hd'
      obtain ⟨a, rfl⟩ := hd
      obtain ⟨b, rfl⟩ := hd'
      have H : (p : ℤ) ∣ 2 := by
        refine ⟨y * a + z * b, ?_⟩
        push_cast at hbez
        linear_combination -hbez
      have H' : p ∣ 2 := by exact_mod_cast H
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp H')
    · exact cancel (he ▸ hq) hd

end multiplicative_nonagonal_additive_eq_id

open multiplicative_nonagonal_additive_eq_id

/-- **Additive uniqueness of generalized nonagonal numbers.** Let $f$ be a multiplicative
arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$ for all
positive integers $a$ and $b$ that are generalized nonagonal numbers, that is, $2a = m(7m - 5)$
and $2b = k(7k - 5)$ for some integers $m$ and $k$. Then $f(n) = n$ for every natural number $n$.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 1
(`integers-2025-A99-thm-1`). -/
public theorem multiplicative_nonagonal_additive_eq_id
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) :
    ∀ n : ℕ, f n = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hsmall : n ≤ 11
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      exact multiplicative_nonagonal_additive_eq_self_of_le_eleven f hf hadd n hn hsmall
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p r hp _ => exact fixed_prime_power hf hadd (r := r) hp rfl (by omega) ih
    | zero => simp
    | one => simpa using hf.map_one
    | coprime a b ha hb hc _ _ =>
      rw [hf.map_mul_of_coprime hc, ih a (by nlinarith), ih b (by nlinarith), Nat.cast_mul]

-- The induction hypothesis is retained to match Theorem 5, though Theorem 1 suffices.
set_option linter.unusedVariables false in
/-- **Nonagonal additive uniqueness: the step at powers of 2.** Let $f$ be a multiplicative
arithmetic function with values in $\mathbb{C}$ such that $f(a + b) = f(a) + f(b)$ for all
positive integers $a$ and $b$ that are generalized nonagonal numbers, that is, $2a = m(7m - 5)$
and $2b = k(7k - 5)$ for some integers $m$ and $k$. Let $r$ be a natural number. If $f(n) = n$
for every natural number $n < 2^r$, then $f(2^r) = 2^r$.

Source: Poo-Sung Park, *On the Additive Uniqueness of Generalized Nonagonal Numbers for
Multiplicative Functions*, INTEGERS 25 (2025), Article A99, Theorem 5
(`integers-2025-A99-thm-5`). -/
public theorem multiplicative_nonagonal_additive_two_pow
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) (r : ℕ)
    (hind : ∀ n : ℕ, n < 2 ^ r → f n = n) :
    f (2 ^ r) = (2 ^ r : ℕ) :=
  multiplicative_nonagonal_additive_eq_id f hf hadd (2 ^ r)

end MetaMathlibExt
