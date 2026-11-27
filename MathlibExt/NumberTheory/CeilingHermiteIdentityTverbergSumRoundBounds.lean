/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.InclExclLikeSumBounds
public import MathlibExt.NumberTheory.InclExclLikeSumRelations
public import MathlibExt.NumberTheory.TverbergSumPeriodic
public import MathlibExt.Algebra.Order.Floor.HalfShift
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity

/-!
# Sharp bounds for Tverberg's sum with rounding half up

Fixing two indices groups the subsets into blocks of four. Each block contributes a signed
second difference of the rounding function, bounded by one in absolute value. When all
coordinates are `r > 0`, `m = 2r`, and `k` is either `0` or `r`, all blocks have the same signed
contribution for that `k`.

The private helpers `split_univ`, `secondDiff` and `secondDiff_bounds` are copied verbatim from
the private helpers of the same names in `MathlibExt.NumberTheory.InclExclLikeSumBounds`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 5.
-/

namespace MetaMathlibExt
namespace tverbergSum_round_bounds

open Finset

private theorem split_univ {n : ℕ} (hn : 2 ≤ n) :
    ∃ (a b : Fin n) (s : Finset (Fin n)), a ∉ insert b s ∧ b ∉ s ∧
      insert a (insert b s) = univ ∧ s.card = n - 2 := by
  obtain ⟨a, t, ha, ht, hc⟩ := card_eq_succ.mp
    (show (univ : Finset (Fin n)).card = (n - 2 + 1) + 1 by simp; omega)
  obtain ⟨b, s, hb, rfl, hs⟩ := card_eq_succ.mp hc
  exact ⟨a, b, s, ha, hb, ht, hs⟩

private theorem neg_one_pow_sub_one {e : ℕ} (he : 1 ≤ e) :
    (-1 : ℤ) ^ (e - 1) = -(-1 : ℤ) ^ e := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
  simp [pow_add]

private theorem neg_one_pow_sub_two {e : ℕ} (he : 2 ≤ e) :
    (-1 : ℤ) ^ (e - 2) = (-1 : ℤ) ^ e := by
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
  simp [pow_add]

private def secondDiff (F : ℝ → ℤ) (a b t : ℝ) : ℤ :=
  F (a + t) + F (b + t) - F t - F (a + (b + t))

private theorem secondDiff_bounds {F : ℝ → ℤ} (hm : Monotone F)
    (hz : ∀ (t : ℝ) (z : ℤ), F (t + z) = F t + z) (a b t : ℝ) :
    -1 ≤ secondDiff F a b t ∧ secondDiff F a b t ≤ 1 := by
  have step (u : ℝ) : F u + ⌊a⌋ ≤ F (a + u) ∧ F (a + u) ≤ F u + ⌊a⌋ + 1 := by
    constructor
    · rw [← hz, add_comm a]
      exact hm (add_le_add_right (Int.floor_le a) _)
    · rw [add_assoc, ← hz, Int.cast_add, Int.cast_one, add_comm a]
      exact hm (add_le_add_right (Int.lt_floor_add_one a).le _)
  have := step t
  have := step (b + t)
  unfold secondDiff
  omega

private theorem block_eq {ℓ : ℕ} {a b : Fin ℓ} {s : Finset (Fin ℓ)}
    (ha : a ∉ insert b s) (hb : b ∉ s) (hc : s.card = ℓ - 2) (hℓ : 2 ≤ ℓ)
    (F : ℝ → ℤ) (x : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) (S : Finset (Fin ℓ))
    (hS : S ∈ s.powerset) :
    ((-1 : ℤ) ^ (ℓ - S.card) * F (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) +
      (-1 : ℤ) ^ (ℓ - (insert b S).card) * F (((k + ∑ i ∈ insert b S, x i : ℤ) : ℝ) / m) +
      (-1 : ℤ) ^ (ℓ - (insert a S).card) * F (((k + ∑ i ∈ insert a S, x i : ℤ) : ℝ) / m) +
      (-1 : ℤ) ^ (ℓ - (insert a (insert b S)).card) *
        F (((k + ∑ i ∈ insert a (insert b S), x i : ℤ) : ℝ) / m)) =
      (-1 : ℤ) ^ (ℓ - S.card) *
        (F (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) -
          F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x b : ℤ) : ℝ) / m) -
          F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m) +
          F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m + ((x b : ℤ) : ℝ) / m)) := by
  have hsub := mem_powerset.mp hS
  have hbS : b ∉ S := notMem_mono hsub hb
  have haS : a ∉ S := notMem_mono (hsub.trans (subset_insert b s)) ha
  have habS : a ∉ insert b S := notMem_mono (insert_subset_insert b hsub) ha
  have cb : (insert b S).card = S.card + 1 := card_insert_of_notMem hbS
  have ca : (insert a S).card = S.card + 1 := card_insert_of_notMem haS
  have cab : (insert a (insert b S)).card = S.card + 2 := by
    simp [card_insert_of_notMem habS, cb]
  have hle : S.card ≤ ℓ - 2 := by
    calc S.card ≤ s.card := card_le_card hsub
    _ = ℓ - 2 := hc
  have he : 2 ≤ ℓ - S.card := by omega
  have he1 : 1 ≤ ℓ - S.card := by omega
  have sb : (-1 : ℤ) ^ (ℓ - (insert b S).card) = -(-1 : ℤ) ^ (ℓ - S.card) := by
    rw [cb]
    have : ℓ - (S.card + 1) = (ℓ - S.card) - 1 := by omega
    rw [this, neg_one_pow_sub_one he1]
  have sa : (-1 : ℤ) ^ (ℓ - (insert a S).card) = -(-1 : ℤ) ^ (ℓ - S.card) := by
    rw [ca]
    have : ℓ - (S.card + 1) = (ℓ - S.card) - 1 := by omega
    rw [this, neg_one_pow_sub_one he1]
  have sab : (-1 : ℤ) ^ (ℓ - (insert a (insert b S)).card) = (-1 : ℤ) ^ (ℓ - S.card) := by
    rw [cab]
    have : ℓ - (S.card + 2) = (ℓ - S.card) - 2 := by omega
    rw [this, neg_one_pow_sub_two he]
  have hb_sum : ∑ i ∈ insert b S, x i = x b + ∑ i ∈ S, x i := sum_insert hbS
  have ha_sum : ∑ i ∈ insert a S, x i = x a + ∑ i ∈ S, x i := sum_insert haS
  have hab_sum : ∑ i ∈ insert a (insert b S), x i = x a + (x b + ∑ i ∈ S, x i) := by
    rw [sum_insert habS, hb_sum]
  have arg_b : (((k + ∑ i ∈ insert b S, x i : ℤ) : ℝ) / m) =
      (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x b : ℤ) : ℝ) / m := by
    rw [hb_sum]
    push_cast
    rw [add_div]
    ring
  have arg_a : (((k + ∑ i ∈ insert a S, x i : ℤ) : ℝ) / m) =
      (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m := by
    rw [ha_sum]
    push_cast
    rw [add_div]
    ring
  have arg_ab : (((k + ∑ i ∈ insert a (insert b S), x i : ℤ) : ℝ) / m) =
      (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m + ((x b : ℤ) : ℝ) / m := by
    rw [hab_sum]
    push_cast
    rw [add_div, add_div]
    ring
  rw [sb, sa, sab, arg_b, arg_a, arg_ab]
  ring

private theorem grouped_sum {ℓ : ℕ} {a b : Fin ℓ} {s : Finset (Fin ℓ)}
    (ha : a ∉ insert b s) (hb : b ∉ s) (hu : insert a (insert b s) = univ)
    (F : ℝ → ℤ) (x : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) :
    tverbergSum F x m k =
      ∑ S ∈ s.powerset, ((-1 : ℤ) ^ (ℓ - S.card) * F (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) +
        (-1 : ℤ) ^ (ℓ - (insert b S).card) * F (((k + ∑ i ∈ insert b S, x i : ℤ) : ℝ) / m) +
        (-1 : ℤ) ^ (ℓ - (insert a S).card) * F (((k + ∑ i ∈ insert a S, x i : ℤ) : ℝ) / m) +
        (-1 : ℤ) ^ (ℓ - (insert a (insert b S)).card) *
          F (((k + ∑ i ∈ insert a (insert b S), x i : ℤ) : ℝ) / m)) := by
  unfold tverbergSum
  have h1 : (∑ T : Finset (Fin ℓ), (-1 : ℤ) ^ (ℓ - T.card) * F (((k + ∑ i ∈ T, x i : ℤ) : ℝ) / m))
      = ∑ T ∈ (univ : Finset (Fin ℓ)).powerset,
          (-1 : ℤ) ^ (ℓ - T.card) * F (((k + ∑ i ∈ T, x i : ℤ) : ℝ) / m) := by
    rw [powerset_univ]
  rw [h1, ← hu]
  rw [sum_powerset_insert ha]
  have g1 : (∑ T ∈ (insert b s).powerset,
      (-1 : ℤ) ^ (ℓ - T.card) * F (((k + ∑ i ∈ T, x i : ℤ) : ℝ) / m)) =
      ∑ S ∈ s.powerset, (((-1 : ℤ) ^ (ℓ - S.card) * F (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m)) +
        ((-1 : ℤ) ^ (ℓ - (insert b S).card) * F (((k + ∑ i ∈ insert b S, x i : ℤ) : ℝ) / m))) := by
    rw [sum_powerset_insert hb, ← sum_add_distrib]
  have g2 : (∑ T ∈ (insert b s).powerset,
      (-1 : ℤ) ^ (ℓ - (insert a T).card) * F (((k + ∑ i ∈ insert a T, x i : ℤ) : ℝ) / m)) =
      ∑ S ∈ s.powerset, (((-1 : ℤ) ^ (ℓ - (insert a S).card) *
          F (((k + ∑ i ∈ insert a S, x i : ℤ) : ℝ) / m)) +
        ((-1 : ℤ) ^ (ℓ - (insert a (insert b S)).card) *
          F (((k + ∑ i ∈ insert a (insert b S), x i : ℤ) : ℝ) / m))) := by
    rw [sum_powerset_insert hb, ← sum_add_distrib]
  rw [g1, g2, ← sum_add_distrib]
  refine sum_congr rfl fun S _ => ?_
  ring

private theorem tverberg_bounds_aux {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (F : ℝ → ℤ)
    (hm : Monotone F) (hz : ∀ (t : ℝ) (z : ℤ), F (t + z) = F t + z)
    (x : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) :
    -2 ^ (ℓ - 2) ≤ tverbergSum F x m k ∧ tverbergSum F x m k ≤ 2 ^ (ℓ - 2) := by
  obtain ⟨a, b, s, ha, hb, hu, hc⟩ := split_univ hℓ
  let term (S : Finset (Fin ℓ)) :=
    (-1 : ℤ) ^ (ℓ - S.card) *
      (F (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) -
        F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x b : ℤ) : ℝ) / m) -
        F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m) +
        F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m + ((x b : ℤ) : ℝ) / m))
  have heq : tverbergSum F x m k = ∑ S ∈ s.powerset, term S := by
    rw [grouped_sum ha hb hu]
    refine sum_congr rfl fun S hS => ?_
    rw [block_eq ha hb hc hℓ F x m k S hS]
  have hterm (S : Finset (Fin ℓ)) (_hS : S ∈ s.powerset) : -1 ≤ term S ∧ term S ≤ 1 := by
    have hD := secondDiff_bounds hm hz (((x a : ℤ) : ℝ) / m) (((x b : ℤ) : ℝ) / m)
      (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m)
    have hDeq : (F (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) -
        F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x b : ℤ) : ℝ) / m) -
        F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m) +
        F ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m + ((x b : ℤ) : ℝ) / m)) =
        -secondDiff F (((x a : ℤ) : ℝ) / m) (((x b : ℤ) : ℝ) / m)
          (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) := by
      unfold secondDiff
      have e1 : ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x b : ℤ) : ℝ) / m) =
          ((x b : ℤ) : ℝ) / m + (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) := add_comm _ _
      have e2 : ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m) =
          ((x a : ℤ) : ℝ) / m + (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) := add_comm _ _
      have e3 : ((((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m) + ((x a : ℤ) : ℝ) / m + ((x b : ℤ) : ℝ) / m) =
          ((x a : ℤ) : ℝ) / m + (((x b : ℤ) : ℝ) / m + (((k + ∑ i ∈ S, x i : ℤ) : ℝ) / m)) := by
        ring
      rw [e3, e1, e2]
      ring
    simp only [term, hDeq]
    rcases neg_one_pow_eq_or ℤ (ℓ - S.card) with hsign | hsign <;>
      simp only [hsign, one_mul, neg_one_mul, neg_neg] <;> omega
  have hcard : (s.powerset.card : ℤ) = 2 ^ (ℓ - 2) := by
    rw [card_powerset, hc]
    push_cast
    rfl
  rw [heq]
  have lower := sum_le_sum (s := s.powerset) (fun S hS => (hterm S hS).1)
  have upper := sum_le_sum (s := s.powerset) (fun S hS => (hterm S hS).2)
  simp only [sum_const, nsmul_eq_mul, hcard, mul_neg, mul_one] at lower upper
  omega

private theorem round_int_add_half (z : ℤ) : round ((z : ℝ) + 1 / 2) = z + 1 := by
  have h : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
  rw [h, round_intCast_add]
  simp

private theorem round_nat_add_half (j : ℕ) : round ((j : ℝ) + 1 / 2) = (j : ℤ) + 1 := by
  have h : ((j : ℝ) + 1 / 2) = ((j : ℤ) : ℝ) + 1 / 2 := by push_cast; ring
  rw [h, round_int_add_half]

private theorem sharp_D0_even (j : ℕ) :
    (round ((((2 * j : ℕ) : ℝ)) / 2) -
      round ((((2 * j : ℕ) : ℝ)) / 2 + 1 / 2) -
      round ((((2 * j : ℕ) : ℝ)) / 2 + 1 / 2) +
      round ((((2 * j : ℕ) : ℝ)) / 2 + 1 / 2 + 1 / 2)) = -1 := by
  have h0 : ((((2 * j : ℕ) : ℝ)) / 2) = (j : ℝ) := by push_cast; ring
  rw [h0]
  have h2 : ((j : ℝ) + 1 / 2 + 1 / 2) = (((j : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [h2, round_nat_add_half]
  simp

private theorem sharp_D0_odd (j : ℕ) :
    (round ((((2 * j + 1 : ℕ) : ℝ)) / 2) -
      round ((((2 * j + 1 : ℕ) : ℝ)) / 2 + 1 / 2) -
      round ((((2 * j + 1 : ℕ) : ℝ)) / 2 + 1 / 2) +
      round ((((2 * j + 1 : ℕ) : ℝ)) / 2 + 1 / 2 + 1 / 2)) = 1 := by
  have h0 : ((((2 * j + 1 : ℕ) : ℝ)) / 2) = (j : ℝ) + 1 / 2 := by push_cast; ring
  rw [h0]
  have h1 : ((j : ℝ) + 1 / 2 + 1 / 2) = (((j : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [h1, round_nat_add_half, round_int_add_half]
  simp
  ring

private theorem sharp_D1_even (j : ℕ) :
    (round (((((2 * j : ℕ) : ℝ)) + 1) / 2) -
      round (((((2 * j : ℕ) : ℝ)) + 1) / 2 + 1 / 2) -
      round (((((2 * j : ℕ) : ℝ)) + 1) / 2 + 1 / 2) +
      round (((((2 * j : ℕ) : ℝ)) + 1) / 2 + 1 / 2 + 1 / 2)) = 1 := by
  have h0 : (((((2 * j : ℕ) : ℝ)) + 1) / 2) = (j : ℝ) + 1 / 2 := by push_cast; ring
  rw [h0]
  have h1 : ((j : ℝ) + 1 / 2 + 1 / 2) = (((j : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [h1, round_nat_add_half, round_int_add_half]
  simp
  ring

private theorem sharp_D1_odd (j : ℕ) :
    (round (((((2 * j + 1 : ℕ) : ℝ)) + 1) / 2) -
      round (((((2 * j + 1 : ℕ) : ℝ)) + 1) / 2 + 1 / 2) -
      round (((((2 * j + 1 : ℕ) : ℝ)) + 1) / 2 + 1 / 2) +
      round (((((2 * j + 1 : ℕ) : ℝ)) + 1) / 2 + 1 / 2 + 1 / 2)) = -1 := by
  have h0 : (((((2 * j + 1 : ℕ) : ℝ)) + 1) / 2) = (((j : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [h0]
  have h2 : ((((j : ℤ) + 1 : ℤ) : ℝ) + 1 / 2 + 1 / 2) = ((((j : ℤ) + 2 : ℤ)) : ℝ) := by
    push_cast; ring
  rw [h2, round_int_add_half]
  simp
  ring

private theorem sign_even {ℓ n j : ℕ} (h : n = 2 * j) (hle : n ≤ ℓ) :
    (-1 : ℤ) ^ (ℓ - n) = (-1 : ℤ) ^ ℓ := by
  have hEven : Even n := ⟨j, by omega⟩
  have hpow : (-1 : ℤ) ^ n = 1 := hEven.neg_one_pow
  have hsplit : ℓ = (ℓ - n) + n := (Nat.sub_add_cancel hle).symm
  have hmul : (-1 : ℤ) ^ ℓ = (-1 : ℤ) ^ (ℓ - n) * (-1 : ℤ) ^ n := by
    conv_lhs => rw [hsplit]
    rw [pow_add]
  rw [hpow, mul_one] at hmul
  exact hmul.symm

private theorem sign_odd {ℓ n j : ℕ} (h : n = 2 * j + 1) (hle : n ≤ ℓ) :
    (-1 : ℤ) ^ (ℓ - n) = -(-1 : ℤ) ^ ℓ := by
  have hOdd : Odd n := ⟨j, h⟩
  have hpow : (-1 : ℤ) ^ n = -1 := hOdd.neg_one_pow
  have hsplit : ℓ = (ℓ - n) + n := (Nat.sub_add_cancel hle).symm
  have hmul : (-1 : ℤ) ^ ℓ = (-1 : ℤ) ^ (ℓ - n) * (-1 : ℤ) ^ n := by
    conv_lhs => rw [hsplit]
    rw [pow_add]
  rw [hpow, mul_neg, mul_one] at hmul
  omega

private theorem neg_one_pow_succ (ℓ : ℕ) : (-1 : ℤ) ^ (ℓ + 1) = -(-1 : ℤ) ^ ℓ := by
  simp [pow_add]

private theorem sharp0 {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (r : ℕ) (hr : 0 < r) :
    tverbergSum round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 =
      (-1 : ℤ) ^ (ℓ + 1) * 2 ^ (ℓ - 2) := by
  obtain ⟨a, b, s, ha, hb, hu, hc⟩ := split_univ hℓ
  rw [grouped_sum ha hb hu]
  trans ∑ _ ∈ s.powerset, (-1 : ℤ) ^ (ℓ + 1)
  · refine sum_congr rfl fun S hS => ?_
    rw [block_eq ha hb hc hℓ round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 S hS]
    have hsub := mem_powerset.mp hS
    have hle2 : S.card ≤ ℓ - 2 := by
      calc S.card ≤ s.card := card_le_card hsub
      _ = ℓ - 2 := hc
    have hle : S.card ≤ ℓ := by omega
    have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
    have hsum : ∑ i ∈ S, (fun _ : Fin ℓ => (r : ℤ)) i = (S.card : ℤ) * r := by simp [sum_const]
    have ht : ((((0 + ∑ i ∈ S, (fun _ : Fin ℓ => (r : ℤ)) i : ℤ) : ℝ) / ((2 * r : ℕ) : ℝ))) =
        (S.card : ℝ) / 2 := by
      rw [hsum]
      push_cast
      field_simp
      ring
    have hA : ((((fun _ : Fin ℓ => (r : ℤ)) a : ℤ) : ℝ) / ((2 * r : ℕ) : ℝ)) = 1 / 2 := by
      have : (fun _ : Fin ℓ => (r : ℤ)) a = (r : ℤ) := rfl
      rw [this]
      push_cast
      field_simp
    simp only [ht, hA]
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' S.card
    · have hD : (round ((S.card : ℝ) / 2) - round ((S.card : ℝ) / 2 + 1 / 2) -
          round ((S.card : ℝ) / 2 + 1 / 2) + round ((S.card : ℝ) / 2 + 1 / 2 + 1 / 2)) = -1 := by
        rw [hj]
        exact sharp_D0_even j
      have hsign : (-1 : ℤ) ^ (ℓ - S.card) = (-1 : ℤ) ^ ℓ := sign_even hj hle
      rw [hD, hsign, neg_one_pow_succ]
      ring
    · have hD : (round ((S.card : ℝ) / 2) - round ((S.card : ℝ) / 2 + 1 / 2) -
          round ((S.card : ℝ) / 2 + 1 / 2) + round ((S.card : ℝ) / 2 + 1 / 2 + 1 / 2)) = 1 := by
        rw [hj]
        exact sharp_D0_odd j
      have hsign : (-1 : ℤ) ^ (ℓ - S.card) = -(-1 : ℤ) ^ ℓ := sign_odd hj hle
      rw [hD, hsign, neg_one_pow_succ]
      ring
  · rw [sum_const, card_powerset, hc, nsmul_eq_mul]
    push_cast
    ring

private theorem sharp1 {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (r : ℕ) (hr : 0 < r) :
    tverbergSum round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r =
      (-1 : ℤ) ^ ℓ * 2 ^ (ℓ - 2) := by
  obtain ⟨a, b, s, ha, hb, hu, hc⟩ := split_univ hℓ
  rw [grouped_sum ha hb hu]
  trans ∑ _ ∈ s.powerset, (-1 : ℤ) ^ ℓ
  · refine sum_congr rfl fun S hS => ?_
    rw [block_eq ha hb hc hℓ round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r S hS]
    have hsub := mem_powerset.mp hS
    have hle2 : S.card ≤ ℓ - 2 := by
      calc S.card ≤ s.card := card_le_card hsub
      _ = ℓ - 2 := hc
    have hle : S.card ≤ ℓ := by omega
    have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
    have hsum : ∑ i ∈ S, (fun _ : Fin ℓ => (r : ℤ)) i = (S.card : ℤ) * r := by simp [sum_const]
    have ht : ((((↑r + ∑ i ∈ S, (fun _ : Fin ℓ => (r : ℤ)) i : ℤ) : ℝ) / ((2 * r : ℕ) : ℝ))) =
        ((S.card : ℝ) + 1) / 2 := by
      rw [hsum]
      push_cast
      field_simp
      ring
    have hA : ((((fun _ : Fin ℓ => (r : ℤ)) a : ℤ) : ℝ) / ((2 * r : ℕ) : ℝ)) = 1 / 2 := by
      have : (fun _ : Fin ℓ => (r : ℤ)) a = (r : ℤ) := rfl
      rw [this]
      push_cast
      field_simp
    simp only [ht, hA]
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' S.card
    · have hD : (round (((S.card : ℝ) + 1) / 2) - round (((S.card : ℝ) + 1) / 2 + 1 / 2) -
          round (((S.card : ℝ) + 1) / 2 + 1 / 2) +
          round (((S.card : ℝ) + 1) / 2 + 1 / 2 + 1 / 2)) = 1 := by
        rw [hj]
        exact sharp_D1_even j
      have hsign : (-1 : ℤ) ^ (ℓ - S.card) = (-1 : ℤ) ^ ℓ := sign_even hj hle
      rw [hD, hsign]
      ring
    · have hD : (round (((S.card : ℝ) + 1) / 2) - round (((S.card : ℝ) + 1) / 2 + 1 / 2) -
          round (((S.card : ℝ) + 1) / 2 + 1 / 2) +
          round (((S.card : ℝ) + 1) / 2 + 1 / 2 + 1 / 2)) = -1 := by
        rw [hj]
        exact sharp_D1_odd j
      have hsign : (-1 : ℤ) ^ (ℓ - S.card) = -(-1 : ℤ) ^ ℓ := sign_odd hj hle
      rw [hD, hsign]
      ring
  · rw [sum_const, card_powerset, hc, nsmul_eq_mul]
    push_cast
    ring

private theorem round_mono : Monotone (round : ℝ → ℤ) := by
  intro u v huv
  simpa only [round_eq] using Int.floor_mono (add_le_add_left huv (1 / 2))

end tverbergSum_round_bounds

open tverbergSum_round_bounds in
/-- **Sharp bounds for Tverberg's sum with rounding half up.** Let $\ell \ge 2$ and let $F$ be
rounding to the nearest integer with ties rounded up, $F(y) = \lfloor y + 1/2 \rfloor$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. Then $-2^{\ell-2} \le f(a, m, k) \le 2^{\ell-2}$ for
all such $a$, $m$ and $k$. Both bounds are attained: for every integer $r \ge 1$, if $a_i = r$
for all $i$ and $m = 2r$, then $f(a, m, 0) = (-1)^{\ell+1} 2^{\ell-2}$ and
$f(a, m, r) = (-1)^{\ell} 2^{\ell-2}$.

The paper states the equality cases separately for odd and even $\ell$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 5. -/
public theorem tverbergSum_round_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum round a m k ∧ tverbergSum round a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 = (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2) ∧
          tverbergSum round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r = (-1) ^ ℓ * 2 ^ (ℓ - 2) := by
  constructor
  · intro a m k
    exact tverberg_bounds_aux hℓ round round_mono round_add_intCast a m k
  · intro r hr
    exact ⟨sharp0 hℓ r hr, sharp1 hℓ r hr⟩

end MetaMathlibExt
