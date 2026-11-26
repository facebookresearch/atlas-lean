/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FloorCeilingSums
public import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Bounds for the four inclusion-exclusion-like sums

Fixing two indices groups the subsets into blocks of four. Each block contributes a signed
second difference of the rounding function. For constant coordinates its sign can be computed
from the parity of the number of remaining indices.
-/

namespace MetaMathlibExt
namespace inclExclLikeSum_bounds_summary

open Finset

private theorem split_univ {n : ℕ} (hn : 2 ≤ n) :
    ∃ (a b : Fin n) (s : Finset (Fin n)), a ∉ insert b s ∧ b ∉ s ∧
      insert a (insert b s) = univ ∧ s.card = n - 2 := by
  obtain ⟨a, t, ha, ht, hc⟩ := card_eq_succ.mp
    (show (univ : Finset (Fin n)).card = (n - 2 + 1) + 1 by simp; omega)
  obtain ⟨b, s, hb, rfl, hs⟩ := card_eq_succ.mp hc
  exact ⟨a, b, s, ha, hb, ht, hs⟩

private def alternating {α : Type*} (s : Finset α) (f : Finset α → ℤ) : ℤ :=
  ∑ T ∈ s.powerset, (-1) ^ T.card * f T

private theorem alternating_insert {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∉ s) (f : Finset α → ℤ) :
    alternating (insert a s) f = alternating s (fun T => f T - f (insert a T)) := by
  simp only [alternating, sum_powerset_insert ha, mul_sub, sum_sub_distrib]
  rw [← sub_neg_eq_add, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun T hT => ?_
  rw [card_insert_of_notMem (notMem_mono (mem_powerset.mp hT) ha), pow_succ]
  ring

-- The model f may take any value at the empty set, which is absent from the original sum.
private theorem grouped {n : ℕ} {a b : Fin n} {s : Finset (Fin n)}
    (ha : a ∉ insert b s) (hb : b ∉ s) (hu : insert a (insert b s) = univ)
    (F : ℝ → ℤ) (x : Fin n → ℝ) (f : Finset (Fin n) → ℤ)
    (hf : ∀ T, T.Nonempty → F (∑ i ∈ T, x i) = f T) :
    inclExclLikeSum F x = f ∅ + ∑ T ∈ s.powerset, (-1) ^ T.card *
      (f (insert a T) + f (insert b T) - f T - f (insert a (insert b T))) := by
  calc
    _ = f ∅ - alternating univ f := by
      rw [inclExclLikeSum, alternating, powerset_univ, sum_filter]
      rw [show f ∅ = ∑ T : Finset (Fin n), (if T = ∅ then f ∅ else 0) by simp,
        ← sum_sub_distrib]
      refine sum_congr rfl fun T _ => ?_
      rcases T.eq_empty_or_nonempty with rfl | h
      · simp
      · rw [ite_eq_left h, hf T h, ite_eq_right h.ne_empty]
        have hk := card_pos.mpr h
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
        simp [hk, pow_succ]
    _ = _ := by
      rw [← hu, alternating_insert ha, alternating_insert hb]
      simp only [alternating, sub_eq_add_neg, ← sum_neg_distrib]
      congr 1
      exact sum_congr rfl fun T _ => by ring

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

-- Isolate the empty block: for floor its contribution is nonpositive, for ceiling nonnegative.
private theorem bounds {n : ℕ} (hn : 2 ≤ n) (F : ℝ → ℤ) (h0 : F 0 = 0)
    (hm : Monotone F) (hz : ∀ (t : ℝ) (z : ℤ), F (t + z) = F t + z)
    (lo hi : ℤ) (hbase : ∀ a b, lo ≤ secondDiff F a b 0 ∧ secondDiff F a b 0 ≤ hi)
    (x : Fin n → ℝ) :
    lo - (2 ^ (n - 2) - 1) ≤ inclExclLikeSum F x ∧
      inclExclLikeSum F x ≤ hi + (2 ^ (n - 2) - 1) := by
  obtain ⟨a, b, s, ha, hb, hu, hc⟩ := split_univ hn
  let term (T : Finset (Fin n)) :=
    (-1 : ℤ) ^ T.card * secondDiff F (x a) (x b) (∑ i ∈ T, x i)
  have he : ∅ ∈ s.powerset := empty_mem_powerset _
  have heq : inclExclLikeSum F x = term ∅ + ∑ T ∈ s.powerset.erase ∅, term T := by
    rw [grouped ha hb hu F x (fun T => F (∑ i ∈ T, x i)) (fun _ _ => rfl)]
    simp only [sum_empty, h0, zero_add]
    rw [add_sum_erase _ term he]
    refine sum_congr rfl fun T hT => ?_
    have hsub := mem_powerset.mp hT
    have hbT := notMem_mono hsub hb
    have haT := notMem_mono (hsub.trans (subset_insert b s)) ha
    have habT := notMem_mono (insert_subset_insert b hsub) ha
    simp only [term, secondDiff, sum_insert hbT, sum_insert haT, sum_insert habT]
  have hterm (T : Finset (Fin n)) : -1 ≤ term T ∧ term T ≤ 1 := by
    have h := secondDiff_bounds hm hz (x a) (x b) (∑ i ∈ T, x i)
    rcases neg_one_pow_eq_or ℤ T.card with hsign | hsign <;> simp [term, hsign] <;> omega
  have hcard : ((s.powerset.erase ∅).card : ℤ) = 2 ^ (n - 2) - 1 := by
    rw [card_erase_of_mem he, Nat.cast_sub (card_pos.mpr ⟨_, he⟩), card_powerset, hc]
    push_cast
    rfl
  have lower := sum_le_sum (s := s.powerset.erase ∅) (fun T _ => (hterm T).1)
  have upper := sum_le_sum (s := s.powerset.erase ∅) (fun T _ => (hterm T).2)
  simp only [sum_const, nsmul_eq_mul, hcard, mul_neg, mul_one] at lower upper
  have h := hbase (x a) (x b)
  have hzero : term ∅ = secondDiff F (x a) (x b) 0 := by simp [term]
  rw [heq, hzero]
  omega

-- The model k ↦ (k + r) / 2 + d has constant signed second difference for r = 0, 1.
private theorem half_second (k : ℕ) (r d : ℤ) (hr : r = 0 ∨ r = 1) :
    (-1 : ℤ) ^ k * ((((k + 1 : ℕ) + r : ℤ) / 2 + d) + (((k + 1 : ℕ) + r : ℤ) / 2 + d) -
      (((k : ℤ) + r) / 2 + d) - (((k + 2 : ℕ) + r : ℤ) / 2 + d)) = 2 * r - 1 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k <;> rcases hr with rfl | rfl <;>
    simp [pow_add, pow_mul] <;> omega

private theorem diagonal {n : ℕ} (hn : 2 ≤ n) (F : ℝ → ℤ) (c : ℝ) (r d : ℤ)
    (hr : r = 0 ∨ r = 1)
    (h : ∀ k : ℕ, 0 < k → k ≤ n → F (k * c) = ((k : ℤ) + r) / 2 + d) :
    inclExclLikeSum F (fun _ : Fin n => c) = (2 * r - 1) * 2 ^ (n - 2) + d := by
  obtain ⟨a, b, s, ha, hb, hu, hc⟩ := split_univ hn
  let f (T : Finset (Fin n)) := ((T.card : ℤ) + r) / 2 + d
  rw [grouped ha hb hu F _ f (fun T hT => by
    simpa [nsmul_eq_mul, f] using h T.card (card_pos.mpr hT) (by simpa using T.card_le_univ))]
  have hsum : (∑ T ∈ s.powerset, (-1 : ℤ) ^ T.card *
      (f (insert a T) + f (insert b T) - f T - f (insert a (insert b T)))) =
      ∑ _T ∈ s.powerset, (2 * r - 1) := by
    refine sum_congr rfl fun T hT => ?_
    have ht := mem_powerset.mp hT
    simp only [f, card_insert_of_notMem (notMem_mono ht hb),
      card_insert_of_notMem (notMem_mono (ht.trans (subset_insert b s)) ha),
      card_insert_of_notMem (notMem_mono (insert_subset_insert b ht) ha)]
    exact half_second T.card r d hr
  rw [hsum, sum_const, card_powerset, hc, nsmul_eq_mul]
  have he : f ∅ = d := by rcases hr with rfl | rfl <;> simp [f]
  rw [he, Nat.cast_pow, Nat.cast_ofNat]
  ring

private theorem half_values {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k) (hkn : k ≤ n) :
    let q := (k : ℤ) / 2
    let q' := ((k : ℤ) + 1) / 2
    let t := (k : ℝ) * (1 / 2)
    let u := (k : ℝ) * (1 / 2 - 1 / (n : ℝ) ^ 2)
    let v := (k : ℝ) * (1 / 2 + 1 / (n : ℝ) ^ 2)
    (⌊t⌋ = q ∧ ⌈t - 1 / 2⌉ = q ∧ ⌈t⌉ = q' ∧ round t = q') ∧
      (⌊u⌋ = q' - 1 ∧ round u = q) ∧ (⌈v⌉ = q + 1 ∧ ⌈v - 1 / 2⌉ = q') := by
  dsimp only
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hδ : 0 < (k : ℝ) / (n : ℝ) ^ 2 := by positivity
  have hδ' : (k : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hn') (show (0 : ℝ) ≤ n by positivity)]
  have hq : 2 * (↑((k : ℤ) / 2) : ℝ) ≤ k ∧
      (k : ℝ) ≤ 2 * (↑((k : ℤ) / 2) : ℝ) + 1 := by exact_mod_cast (by omega :
        2 * ((k : ℤ) / 2) ≤ k ∧ (k : ℤ) ≤ 2 * ((k : ℤ) / 2) + 1)
  have hq' : 2 * (↑(((k : ℤ) + 1) / 2) : ℝ) - 1 ≤ k ∧
      (k : ℝ) ≤ 2 * (↑(((k : ℤ) + 1) / 2) : ℝ) := by exact_mod_cast (by omega :
        2 * (((k : ℤ) + 1) / 2) - 1 ≤ k ∧ (k : ℤ) ≤ 2 * (((k : ℤ) + 1) / 2))
  simp only [round_eq, Int.floor_eq_iff, Int.ceil_eq_iff, Int.cast_add, Int.cast_sub,
    Int.cast_one, mul_sub, mul_add, mul_one_div]
  obtain ⟨hq₁, hq₂⟩ := hq
  obtain ⟨hq₃, hq₄⟩ := hq'
  repeat' apply And.intro
  all_goals linarith

private theorem rounding_bounds {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    (-2 ^ (n - 2) ≤ inclExclLikeSum Int.floor x ∧
      inclExclLikeSum Int.floor x ≤ 2 ^ (n - 2) - 1) ∧
    (-2 ^ (n - 2) + 1 ≤ inclExclLikeSum Int.ceil x ∧
      inclExclLikeSum Int.ceil x ≤ 2 ^ (n - 2)) ∧
    (-2 ^ (n - 2) ≤ inclExclLikeSum round x ∧ inclExclLikeSum round x ≤ 2 ^ (n - 2)) ∧
    (-2 ^ (n - 2) ≤ inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ≤ 2 ^ (n - 2)) := by
  have floorBase (a b : ℝ) : -1 ≤ secondDiff Int.floor a b 0 ∧ secondDiff Int.floor a b 0 ≤ 0 := by
    have hlo := Int.le_floor_add_floor a b
    have hhi := Int.le_floor_add a b
    simp only [secondDiff, add_zero, Int.floor_zero, sub_zero]
    omega
  have ceilBase (a b : ℝ) : 0 ≤ secondDiff Int.ceil a b 0 ∧ secondDiff Int.ceil a b 0 ≤ 1 := by
    have h := (secondDiff_bounds Int.ceil_mono Int.ceil_add_intCast a b 0).2
    exact ⟨by simpa [secondDiff, sub_nonneg] using Int.ceil_add_le a b, h⟩
  have symmBounds (F : ℝ → ℤ) (h0 : F 0 = 0) (hm : Monotone F)
      (hz : ∀ (t : ℝ) (z : ℤ), F (t + z) = F t + z) :
      -2 ^ (n - 2) ≤ inclExclLikeSum F x ∧ inclExclLikeSum F x ≤ 2 ^ (n - 2) := by
    have := bounds hn F h0 hm hz (-1) 1 (fun a b => secondDiff_bounds hm hz a b 0) x
    omega
  refine ⟨?_, ?_, symmBounds round round_zero ?_ round_add_intCast, symmBounds _ ?_ ?_ ?_⟩
  · have := bounds hn _ Int.floor_zero Int.floor_mono Int.floor_add_intCast (-1) 0 floorBase x
    omega
  · have := bounds hn _ Int.ceil_zero Int.ceil_mono Int.ceil_add_intCast 0 1 ceilBase x
    omega
  · intro u v huv
    simpa only [round_eq] using Int.floor_mono (add_le_add_left huv (1 / 2))
  · norm_num [Int.ceil_eq_iff]
  · exact fun _ _ huv => Int.ceil_mono (sub_le_sub_right huv _)
  · intro t z
    simpa only [add_sub_right_comm] using Int.ceil_add_intCast (t - 1 / 2) z

end inclExclLikeSum_bounds_summary

open inclExclLikeSum_bounds_summary in
/-- **Bounds for the four inclusion-exclusion-like sums.** Let $n \ge 2$ and write $g_1$, $g_2$,
$g_3$, $g_4$ for the inclusion-exclusion-like sums $g^{(F)}$ in $n$ real variables with $F$ the
floor function $\lfloor y \rfloor$, the ceiling function $\lceil y \rceil$, the nearest-integer
function $\lfloor y + 1/2 \rfloor$ (ties rounded up) and $\lceil y - 1/2 \rceil$ (ties rounded
down), respectively. Then for every $x \in \mathbb{R}^n$,
$-2^{n-2} \le g_1(x) \le 2^{n-2} - 1$, $-2^{n-2} + 1 \le g_2(x) \le 2^{n-2}$,
$-2^{n-2} \le g_3(x) \le 2^{n-2}$ and $-2^{n-2} \le g_4(x) \le 2^{n-2}$. At the point with all
coordinates $1/2$, $g_1 = g_4 = -2^{n-2}$ and $g_2 = g_3 = 2^{n-2}$. At the point with all
coordinates $1/2 - 1/n^2$, $g_1 = 2^{n-2} - 1 = -g_3 - 1$. At the point with all coordinates
$1/2 + 1/n^2$, $g_2 = -2^{n-2} + 1 = -g_4 + 1$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Corollary 1. -/
public theorem inclExclLikeSum_bounds_summary {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ,
      (-2 ^ (n - 2) ≤ inclExclLikeSum Int.floor x ∧
        inclExclLikeSum Int.floor x ≤ 2 ^ (n - 2) - 1) ∧
      (-2 ^ (n - 2) + 1 ≤ inclExclLikeSum Int.ceil x ∧
        inclExclLikeSum Int.ceil x ≤ 2 ^ (n - 2)) ∧
      (-2 ^ (n - 2) ≤ inclExclLikeSum round x ∧ inclExclLikeSum round x ≤ 2 ^ (n - 2)) ∧
      (-2 ^ (n - 2) ≤ inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ∧
        inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ≤ 2 ^ (n - 2))) ∧
    (inclExclLikeSum Int.floor (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2) ∧
      inclExclLikeSum round (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2)) ∧
    (inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) = 2 ^ (n - 2) - 1 ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) =
        -inclExclLikeSum round (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) - 1) ∧
    (inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) = -2 ^ (n - 2) + 1 ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) =
        -inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉)
          (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) + 1) := by
  have lowerHalf (F : ℝ → ℤ) (c : ℝ) (d : ℤ)
      (h : ∀ k : ℕ, 0 < k → k ≤ n → F (k * c) = (k : ℤ) / 2 + d) :
      inclExclLikeSum F (fun _ : Fin n => c) = -2 ^ (n - 2) + d := by
    simpa using diagonal hn F c 0 d (Or.inl rfl) (by simpa using h)
  have upperHalf (F : ℝ → ℤ) (c : ℝ) (d : ℤ)
      (h : ∀ k : ℕ, 0 < k → k ≤ n → F (k * c) = ((k : ℤ) + 1) / 2 + d) :
      inclExclLikeSum F (fun _ : Fin n => c) = 2 ^ (n - 2) + d := by
    simpa using diagonal hn F c 1 d (Or.inr rfl) h
  refine ⟨rounding_bounds hn, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simpa using lowerHalf Int.floor (1 / 2) 0 (fun k hk hkn => by
      simpa using (half_values hn hk hkn).1.1)
  · simpa using lowerHalf (fun y : ℝ => ⌈y - 1 / 2⌉) (1 / 2) 0 (fun k hk hkn => by
      simpa using (half_values hn hk hkn).1.2.1)
  · simpa using upperHalf Int.ceil (1 / 2) 0 (fun k hk hkn => by
      simpa using (half_values hn hk hkn).1.2.2.1)
  · simpa using upperHalf round (1 / 2) 0 (fun k hk hkn => by
      simpa using (half_values hn hk hkn).1.2.2.2)
  · have hf := upperHalf Int.floor (1 / 2 - 1 / (n : ℝ) ^ 2) (-1) (fun k hk hkn =>
      (half_values hn hk hkn).2.1.1)
    have hr := lowerHalf round (1 / 2 - 1 / (n : ℝ) ^ 2) 0 (fun k hk hkn => by
      simpa using (half_values hn hk hkn).2.1.2)
    omega
  · have hc := lowerHalf Int.ceil (1 / 2 + 1 / (n : ℝ) ^ 2) 1 (fun k hk hkn =>
      (half_values hn hk hkn).2.2.1)
    have hr := upperHalf (fun y : ℝ => ⌈y - 1 / 2⌉) (1 / 2 + 1 / (n : ℝ) ^ 2) 0
      (fun k hk hkn => by simpa using (half_values hn hk hkn).2.2.2)
    omega

/-- **Extrema of the ceiling inclusion-exclusion-like sum.** Let $n \ge 2$ and let $g_2$ be the
inclusion-exclusion-like sum $g^{(F)}$ in $n$ real variables with $F$ the ceiling function. Then
$-2^{n-2} + 1 \le g_2(x) \le 2^{n-2}$ for every $x \in \mathbb{R}^n$; the minimum $-2^{n-2} + 1$
is attained at the point with all coordinates $1/2 + 1/n^2$, and the maximum $2^{n-2}$ at the
point with all coordinates $1/2$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 1. -/
public theorem inclExclLikeSum_ceil_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) + 1 ≤ inclExclLikeSum Int.ceil x ∧
      inclExclLikeSum Int.ceil x ≤ 2 ^ (n - 2)) ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) = -2 ^ (n - 2) + 1 ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2) := by
  obtain ⟨hbounds, hhalf, _, habove⟩ := inclExclLikeSum_bounds_summary hn
  exact ⟨fun x => (hbounds x).2.1, habove.1, hhalf.2.2.1⟩

end MetaMathlibExt
