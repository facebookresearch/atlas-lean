/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasures
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lower bounds for the Irwin sum without a nonzero digit

This module proves two strict logarithmic lower bounds for the Irwin sum with digit count zero.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Proposition 2.
-/

namespace MetaMathlibExt

open scoped BigOperators
open Filter

private noncomputable def selected (b d : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 0 < n ∧ digitCount b d n = 0 then f n else 0

private theorem selected_zero (b d : ℕ) (f : ℕ → ℝ) : selected b d f 0 = 0 := by
  simp [selected]

private theorem selected_nonneg (b d : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (n : ℕ) : 0 ≤ selected b d f n := by
  unfold selected
  split
  · exact hf n
  · exact le_rfl

private theorem selected_child (b d n a : ℕ) (hb : 1 < b) (hn : 0 < n) (ha : a < b)
    (f : ℕ → ℝ) :
    selected b d f (b * n + a) =
      if a = d then 0 else selected b d (fun n => f (b * n + a)) n := by
  have hpos : 0 < b * n + a := by positivity
  have he : digitCount b d (b * n + a) = (if a = d then 1 else 0) + digitCount b d n := by
    unfold digitCount
    rw [Nat.add_comm, Nat.digits_add b hb a n ha (Or.inr (Nat.ne_of_gt hn))]
    simp only [List.count_cons, beq_iff_eq, Nat.add_comm]
  by_cases had : a = d
  · rw [ite_eq_left had]
    unfold selected
    rw [ite_eq_right]
    intro h
    rw [he, ite_eq_left had] at h
    omega
  · rw [ite_eq_right had]
    unfold selected
    congr 1
    rw [he, ite_eq_right had]
    simp [hn, hpos]

private theorem sum_blocks (b N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.range (b * N), f n =
      ∑ n ∈ Finset.range N, ∑ a ∈ Finset.range b, f (b * n + a) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

private theorem sum_except (b d : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.range b, if a = d then 0 else f a) =
      ∑ a ∈ (Finset.range b).erase d, f a := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : a = d <;> simp [h]

private theorem reciprocal_children_le (b d n : ℕ) (hb : 1 < b) (hd : d < b) :
    (∑ a ∈ Finset.range b, selected b d (fun n => (1 : ℝ) / n) (b * n + a)) ≤
      ((b : ℝ) - 1) / b * selected b d (fun n => (1 : ℝ) / n) n +
        (if n = 0 then ∑ a ∈ Finset.range b,
          selected b d (fun n => (1 : ℝ) / n) a else 0) := by
  by_cases hn : n = 0
  · simp [hn, selected_zero]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hbR : (0 : ℝ) < b := by positivity
  simp only [ite_eq_right hn, add_zero]
  rw [Finset.sum_congr rfl (fun a ha =>
    selected_child b d n a hb hnpos (Finset.mem_range.mp ha) _)]
  by_cases hc : digitCount b d n = 0
  · simp only [selected, hnpos, hc, and_self, ↓reduceIte]
    rw [sum_except]
    calc
      _ ≤ ∑ a ∈ (Finset.range b).erase d, (1 : ℝ) / ((b : ℝ) * n) := by
        apply Finset.sum_le_sum
        intro a ha
        push_cast
        exact one_div_le_one_div_of_le (by positivity) (le_add_of_nonneg_right (Nat.cast_nonneg a))
      _ = ((b : ℝ) - 1) / b * (1 / n) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_range.mpr hd),
          Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega)]
        push_cast
        ring
  · simp [selected, hc]

private theorem reciprocal_summable (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    Summable (selected b d (fun n => (1 : ℝ) / n)) := by
  let f := selected b d (fun n => (1 : ℝ) / n)
  let C := ∑ a ∈ Finset.range b, f a
  have hf (n : ℕ) : 0 ≤ f n := selected_nonneg b d _ (fun n => by positivity) n
  have hC : 0 ≤ C := Finset.sum_nonneg fun n _ => hf n
  have hbR : (0 : ℝ) < b := by positivity
  have hstep (N : ℕ) (hN : 0 < N) :
      (∑ n ∈ Finset.range (b * N), f n) ≤ C + ((b : ℝ) - 1) / b *
        ∑ n ∈ Finset.range N, f n := by
    rw [sum_blocks]
    calc
      _ ≤ ∑ n ∈ Finset.range N, (((b : ℝ) - 1) / b * f n +
          if n = 0 then C else 0) :=
        Finset.sum_le_sum fun n _ => reciprocal_children_le b d n hb hd
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hN, add_comm]
  have hbound (k : ℕ) : (∑ n ∈ Finset.range (b ^ k), f n) ≤ b * C := by
    induction k with
    | zero => simp [f, selected_zero, mul_nonneg hbR.le hC]
    | succ k ih =>
      rw [pow_succ']
      have h := hstep (b ^ k) (pow_pos (by omega) k)
      have hq : 0 ≤ ((b : ℝ) - 1) / b :=
        div_nonneg (sub_nonneg.mpr (by exact_mod_cast hb.le)) hbR.le
      have he : C + ((b : ℝ) - 1) / b * (b * C) = b * C := by field_simp; ring
      have hm := mul_le_mul_of_nonneg_left ih hq
      linarith
  refine summable_of_sum_range_le (c := b * C) hf ?_
  intro N
  have hN : N ≤ b ^ N := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ]
      have hp : 0 < b ^ N := pow_pos (by omega) _
      nlinarith
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
    (fun n _ _ => hf n)).trans (hbound N)

private noncomputable def increment (n : ℕ) : ℝ := Real.log (1 + 1 / (n : ℝ))

private theorem increment_eq (n : ℕ) :
    increment n = Real.log ((n : ℝ) + 1) - Real.log n := by
  by_cases hn : n = 0
  · simp [hn, increment]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have he : (1 : ℝ) + 1 / n = ((n : ℝ) + 1) / n := by field_simp
  rw [increment, he, Real.log_div (by positivity) hnR]

private theorem increment_nonneg (n : ℕ) : 0 ≤ increment n := by
  exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))

private theorem increment_le (n : ℕ) : increment n ≤ (1 : ℝ) / n := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)
  dsimp [increment]
  linarith

private theorem increment_lt (n : ℕ) (hn : 0 < n) : increment n < (1 : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)
    (ne_of_gt (lt_add_of_pos_right 1 (one_div_pos.mpr hnR)))
  dsimp [increment]
  linarith

private theorem sum_increment (N : ℕ) :
    (∑ n ∈ Finset.range N, increment n) = Real.log N := by
  simp_rw [increment_eq]
  simpa using Finset.sum_range_sub (fun n : ℕ => Real.log n) N

private theorem sum_increment_children (b n : ℕ) (hb : 0 < b) (hn : 0 < n) :
    (∑ a ∈ Finset.range b, increment (b * n + a)) = increment n := by
  simp_rw [increment_eq]
  have he (a : ℕ) : Real.log (((b * n + a : ℕ) : ℝ) + 1) -
      Real.log ((b * n + a : ℕ) : ℝ) =
      Real.log ((b * n + (a + 1) : ℕ) : ℝ) -
        Real.log ((b * n + a : ℕ) : ℝ) := by push_cast; rw [add_assoc]
  rw [Finset.sum_congr rfl (fun a _ => he a),
    Finset.sum_range_sub (fun a : ℕ => Real.log ((b * n + a : ℕ) : ℝ)) b]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  push_cast
  rw [show (b : ℝ) * n + b = b * ((n : ℝ) + 1) by ring,
    Real.log_mul hbR (by positivity), add_zero, Real.log_mul hbR hnR]
  ring

private theorem selected_le (b d : ℕ) (f g : ℕ → ℝ) (h : ∀ n, f n ≤ g n)
    (n : ℕ) : selected b d f n ≤ selected b d g n := by
  unfold selected
  split
  · exact h n
  · exact le_rfl

private theorem increment_summable (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    Summable (selected b d increment) :=
  Summable.of_nonneg_of_le (selected_nonneg b d increment increment_nonneg)
    (selected_le b d _ _ increment_le) (reciprocal_summable b d hb hd)

private theorem excluded_le (b d : ℕ) (hb : 1 < b) (n : ℕ) :
    (b : ℝ) * selected b d (fun n => increment (b * n + d)) n ≤
      selected b d (fun n => (1 : ℝ) / n) n := by
  unfold selected
  split
  · rename_i h
    have hbR : (0 : ℝ) < b := by positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast h.1
    have hp : (0 : ℝ) < (b : ℝ) * n := mul_pos hbR hnR
    have hi := increment_le (b * n + d)
    have hj : (1 : ℝ) / (b * n + d : ℕ) ≤ 1 / ((b : ℝ) * n) := by
      push_cast
      exact one_div_le_one_div_of_le hp (le_add_of_nonneg_right (Nat.cast_nonneg d))
    calc
      _ ≤ b * (1 / ((b : ℝ) * n)) := mul_le_mul_of_nonneg_left (hi.trans hj) hbR.le
      _ = (1 : ℝ) / n := by field_simp
  · simp

private theorem excluded_summable (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    Summable (selected b d (fun n => increment (b * n + d))) := by
  have hs : Summable (fun n => (b : ℝ) *
      selected b d (fun n => increment (b * n + d)) n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg b)
      (selected_nonneg b d _ (fun n => increment_nonneg _) n))
      (excluded_le b d hb) (reciprocal_summable b d hb hd)
  exact (summable_mul_left_iff (show (b : ℝ) ≠ 0 by positivity)).mp hs

private theorem increment_root (b d : ℕ) (hd : d < b) :
    (∑ a ∈ Finset.range b, selected b d increment a) = Real.log b - increment d := by
  have he : (∑ a ∈ Finset.range b, selected b d increment a) =
      ∑ a ∈ Finset.range b, if a = d then 0 else increment a := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases ha0 : a = 0
    · simp [ha0, selected, increment]
    have hap : 0 < a := Nat.pos_of_ne_zero ha0
    have hc : digitCount b d a = if a = d then 1 else 0 := by
      unfold digitCount
      rw [Nat.digits_of_lt b a ha0 (Finset.mem_range.mp ha)]
      simp only [List.count_cons, List.count_nil, zero_add, beq_iff_eq]
    simp only [selected, hap, hc]
    by_cases had : a = d <;> simp [had]
  rw [he, sum_except]
  have h := (Finset.range b).sum_erase_add increment (Finset.mem_range.mpr hd)
  rw [sum_increment] at h
  linarith

private theorem increment_children (b d n : ℕ) (hb : 1 < b) (hd : d < b) :
    (∑ a ∈ Finset.range b, selected b d increment (b * n + a)) =
      selected b d increment n - selected b d (fun n => increment (b * n + d)) n +
        if n = 0 then ∑ a ∈ Finset.range b, selected b d increment a else 0 := by
  by_cases hn : n = 0
  · simp [hn, selected_zero]
  have hnp : 0 < n := Nat.pos_of_ne_zero hn
  rw [ite_eq_right hn, add_zero,
    Finset.sum_congr rfl (fun a ha =>
      selected_child b d n a hb hnp (Finset.mem_range.mp ha) increment)]
  by_cases hc : digitCount b d n = 0
  · simp only [selected, hnp, hc, and_self, ↓reduceIte]
    rw [sum_except]
    have h := (Finset.range b).sum_erase_add (fun a => increment (b * n + a))
      (Finset.mem_range.mpr hd)
    rw [sum_increment_children b n (by omega) hnp] at h
    linarith
  · simp [selected, hc]

private theorem excluded_sum (b d : ℕ) (hb : 1 < b) (hd : d < b) :
    (∑' n : ℕ, selected b d (fun n => increment (b * n + d)) n) =
      Real.log b - increment d := by
  let L := selected b d increment
  let E := selected b d (fun n => increment (b * n + d))
  have he (N : ℕ) (hN : 0 < N) :
      (∑ n ∈ Finset.range N, E n) = Real.log b - increment d +
        (∑ n ∈ Finset.range N, L n) - ∑ n ∈ Finset.range (b * N), L n := by
    have h := sum_blocks b N L
    rw [Finset.sum_congr rfl (fun n _ => increment_children b d n hb hd)] at h
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
    simp only [Finset.sum_ite_eq', Finset.mem_range, hN, ↓reduceIte] at h
    rw [increment_root b d hd] at h
    linarith
  have hL := (increment_summable b d hb hd).hasSum.tendsto_sum_nat
  have hE := (excluded_summable b d hb hd).hasSum.tendsto_sum_nat
  have hmul : Tendsto (fun N : ℕ => b * N) atTop atTop := by
    apply tendsto_atTop_mono (fun N => ?_) tendsto_id
    exact Nat.le_mul_of_pos_left N (by omega)
  have hconst : Tendsto (fun _ : ℕ => Real.log b - increment d) atTop
      (nhds (Real.log b - increment d)) := tendsto_const_nhds
  have hlim := (hconst.add hL).sub (hL.comp hmul)
  have hEq := tendsto_nhds_unique_of_eventuallyEq hE hlim
    ((eventually_gt_atTop 0).mono he)
  simpa using hEq

/-- **Lower bounds for the Irwin sum without the digit.** Let $b > 2$ be a base and let $d$ be a
nonzero digit, $0 < d < b$. Let $H^{(0)}$ be the Irwin sum of $1/n$ over the positive integers $n$
whose base-$b$ expansion does not contain $d$. Then
$b \log b - b \log(1 + 1/d) < H^{(0)}$ and $b \log(b/2) < H^{(0)}$.

Source:
Jean-François Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26
(2026), Article A11, Proposition 2. -/
public theorem irwinSum_zero_lowerBounds
    (b d : ℕ) (hb : 2 < b) (hd : d < b) (hd0 : d ≠ 0) :
    (b : ℝ) * Real.log b - (b : ℝ) * Real.log (1 + 1 / (d : ℝ)) <
      irwinSum b d 0 ∧
    (b : ℝ) * Real.log ((b : ℝ) / 2) < irwinSum b d 0 := by
  have hb1 : 1 < b := by omega
  have hbR : (0 : ℝ) < b := by positivity
  obtain ⟨a, ha, hab, had⟩ : ∃ a : ℕ, 0 < a ∧ a < b ∧ a ≠ d := by
    by_cases h : d = 1
    · exact ⟨2, by omega, hb, by omega⟩
    · exact ⟨1, by omega, hb1, Ne.symm h⟩
  have hc : digitCount b d a = 0 := by
    unfold digitCount
    rw [Nat.digits_of_lt b a (Nat.ne_of_gt ha) hab]
    simp [had]
  have hstrict : (b : ℝ) * selected b d (fun n => increment (b * n + d)) a <
      selected b d (fun n => (1 : ℝ) / n) a := by
    simp only [selected, ha, hc, and_self, ↓reduceIte]
    have hp : (0 : ℝ) < (b : ℝ) * a := by positivity
    have hi := increment_lt (b * a + d) (by positivity)
    have hj : (1 : ℝ) / (b * a + d : ℕ) ≤ 1 / ((b : ℝ) * a) := by
      push_cast
      exact one_div_le_one_div_of_le hp (le_add_of_nonneg_right (Nat.cast_nonneg d))
    calc
      _ < (b : ℝ) * (1 / ((b * a + d : ℕ) : ℝ)) := mul_lt_mul_of_pos_left hi hbR
      _ ≤ b * (1 / ((b : ℝ) * a)) := mul_le_mul_of_nonneg_left hj hbR.le
      _ = (1 : ℝ) / a := by field_simp
  have hlt := Summable.tsum_lt_tsum_of_nonneg
    (fun n => mul_nonneg hbR.le (selected_nonneg b d _ (fun n => increment_nonneg _) n))
    (excluded_le b d hb1) hstrict (reciprocal_summable b d hb1 hd)
  rw [tsum_mul_left, excluded_sum b d hb1 hd] at hlt
  have hfirst : (b : ℝ) * Real.log b - (b : ℝ) *
      Real.log (1 + 1 / (d : ℝ)) < irwinSum b d 0 := by
    simpa only [mul_sub, increment, irwinSum, selected] using hlt
  refine ⟨hfirst, lt_of_le_of_lt ?_ hfirst⟩
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
  have hl : Real.log (1 + 1 / (d : ℝ)) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    have hdiv : (1 : ℝ) / d ≤ 1 := (div_le_one (by positivity)).mpr hdR
    linarith
  rw [Real.log_div (ne_of_gt hbR) two_ne_zero]
  have hm := mul_le_mul_of_nonneg_left hl hbR.le
  nlinarith

end MetaMathlibExt
