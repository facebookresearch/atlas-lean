/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.IrwinSeriesMeasures
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Properties of the complementary moment recurrence

Solutions of the complementary moment recurrence have positive bounded moments, decrease with
the degree except in the binary exceptional row, and decrease with the digit count to the
moments of the uniform measure of mass equal to the base.

Source: Jean-François Burnol, *Measures for the Summation of Irwin Series*,
INTEGERS 26 (2026), Article A11, Theorem 2.
-/

namespace MetaMathlibExt

open Filter Finset

namespace complementaryMomentRecurrence_properties

private def translate (a : ℕ) (v : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1), (m.choose i : ℝ) * (a : ℝ) ^ i * v (m - i)

private def lower (a : ℕ) (v : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Icc 1 m, (m.choose i : ℝ) * (a : ℝ) ^ i * v (m - i)

private theorem translate_split (a : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    translate a v m = v m + lower a v m := by
  have hr : range (m + 1) = insert 0 (Icc 1 m) := by ext i; simp; omega
  simp [translate, lower, hr]

private theorem translate_sub (a : ℕ) (v w : ℕ → ℝ) (m : ℕ) :
    translate a (fun k => v k - w k) m = translate a v m - translate a w m := by
  simp [translate, mul_sub, sum_sub_distrib]

private theorem translate_succ (a : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    translate a v (m + 1) =
      translate a (fun k => v (k + 1)) m + a * translate a v m := by
  unfold translate
  simp only [mul_assoc]
  rw [sum_choose_succ_mul (fun i k => (a : ℝ) ^ i * v k), mul_sum]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    have hi' : m + 1 - i = (m - i) + 1 := by have := mem_range.mp hi; omega
    rw [hi']
  · refine sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring

private theorem translate_nonneg {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) (a m : ℕ) :
    0 ≤ translate a v m :=
  sum_nonneg fun i _ => mul_nonneg (by positivity) (hv _)

private def residual (s : Finset ℕ) (c : ℝ) (v : ℕ → ℝ) (m : ℕ) : ℝ :=
  c * v m - ∑ a ∈ s, translate a v m

private theorem residual_eq (s : Finset ℕ) (c : ℝ) (v : ℕ → ℝ) (m : ℕ) :
    residual s c v m = (c - s.card) * v m - ∑ a ∈ s, lower a v m := by
  simp [residual, translate_split, sum_add_distrib, nsmul_eq_mul]
  ring

private theorem residual_sub (s : Finset ℕ) (c : ℝ) (v w : ℕ → ℝ) (m : ℕ) :
    residual s c (fun k => v k - w k) m = residual s c v m - residual s c w m := by
  simp [residual, translate_sub, sum_sub_distrib]
  ring

private theorem lower_nonneg {m : ℕ} {v : ℕ → ℝ} (hv : ∀ k < m, 0 ≤ v k) (a : ℕ) :
    0 ≤ lower a v m := by
  refine sum_nonneg fun i hi => mul_nonneg (by positivity) (hv _ ?_)
  have := mem_Icc.mp hi
  omega

private theorem nonneg_of_residual {s : Finset ℕ} {c : ℕ → ℝ} {v : ℕ → ℝ}
    (hc : ∀ m, (s.card : ℝ) < c m) (h : ∀ m, 0 ≤ residual s (c m) v m) :
    ∀ m, 0 ≤ v m := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    have he := h m
    rw [residual_eq] at he
    have hs := sum_nonneg (s := s) fun a _ => lower_nonneg ih a
    exact nonneg_of_mul_nonneg_right (by linarith) (sub_pos.mpr (hc m))

private theorem pos_of_residual {s : Finset ℕ} {c : ℝ} {v : ℕ → ℝ} {m : ℕ}
    (hc : (s.card : ℝ) < c) (hv : ∀ k, 0 ≤ v k) (h : 0 < residual s c v m) :
    0 < v m := by
  rw [residual_eq] at h
  have hs := sum_nonneg (s := s) fun a _ => lower_nonneg (m := m) (fun k _ => hv k) a
  exact pos_of_mul_pos_right (by linarith) (sub_nonneg.mpr hc.le)

private abbrev digits (b d : ℕ) := (range b).erase d

private theorem card_digits {b d : ℕ} (hd : d < b) : ((digits b d).card : ℝ) = b - 1 := by
  rw [card_erase_of_mem (mem_range.mpr hd), card_range, Nat.cast_sub (by omega)]
  simp

private theorem coeff_lt {b d : ℕ} (hb : 1 < b) (hd : d < b) (m : ℕ) :
    ((digits b d).card : ℝ) < (b : ℝ) ^ (m + 1) := by
  rw [card_digits hd]
  have hb' : 1 ≤ (b : ℝ) := by exact_mod_cast hb.le
  have hp := pow_le_pow_right₀ hb' (show 1 ≤ m + 1 by omega)
  simp only [pow_one] at hp
  linarith

private theorem sum_lower (b d : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    ∑ a ∈ digits b d, lower a v m =
      ∑ i ∈ Icc 1 m, (m.choose i : ℝ) * digitPowerSum b d i * v (m - i) := by
  unfold lower digitPowerSum
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h (a : ℕ) : (if a = d then 0 else (a : ℝ) ^ i) =
      (if a ≠ d then (a : ℝ) ^ i else 0) := by split_ifs <;> simp_all
  simp_rw [h]
  rw [← sum_filter, filter_ne']
  simp [mul_sum, sum_mul]

private abbrev omitted (b d : ℕ) := b - 1 - d

private theorem omitted_lt {b d : ℕ} (hb : 1 < b) : omitted b d < b := by
  dsimp [omitted]
  omega

private def forcing (b d : ℕ) (v : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, m => (b : ℝ) ^ (m + 1)
  | j + 1, m => translate (omitted b d) (v j) m

private theorem row_eq {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b)
    (hv : ComplementaryMomentRecurrence b d v) (j m : ℕ) :
    residual (digits b (omitted b d)) ((b : ℝ) ^ (m + 1)) (v j) m =
      forcing b d v j m := by
  rw [residual_eq, card_digits (omitted_lt hb), sum_lower]
  have hc : (b : ℝ) ^ (m + 1) - (b - 1) = (b : ℝ) ^ (m + 1) - b + 1 := by ring
  rw [hc]
  cases j with
  | zero =>
    have h := hv.1 m
    change _ = (b : ℝ) ^ (m + 1)
    change ((b : ℝ) ^ (m + 1) - b + 1) * v 0 m =
      (b : ℝ) ^ (m + 1) +
        ∑ i ∈ Icc 1 m, (m.choose i : ℝ) * digitPowerSum b (omitted b d) i * v 0 (m - i) at h
    linarith only [h]
  | succ j =>
    have h := hv.2 (j + 1) (by omega) m
    simpa only [Nat.add_sub_cancel, forcing, translate, complementaryDigitPowerSum, omitted]
      using sub_eq_of_eq_add' h

private theorem degree_zero {b d : ℕ} {v : ℕ → ℕ → ℝ}
    (hv : ComplementaryMomentRecurrence b d v) (j : ℕ) : v j 0 = b := by
  induction j with
  | zero => simpa using hv.1 0
  | succ j ih => simpa [ih] using hv.2 (j + 1) (by omega) 0

private theorem moment_nonneg {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b)
    (hv : ComplementaryMomentRecurrence b d v) (j : ℕ) : ∀ m, 0 ≤ v j m := by
  induction j with
  | zero =>
    refine nonneg_of_residual (coeff_lt hb (omitted_lt (d := d) hb)) ?_
    intro m
    rw [row_eq hb hv]
    change 0 ≤ (b : ℝ) ^ (m + 1)
    positivity
  | succ j ih =>
    refine nonneg_of_residual (coeff_lt hb (omitted_lt (d := d) hb)) ?_
    intro m
    rw [row_eq hb hv]
    exact translate_nonneg ih _ m

private theorem translate_ge {v : ℕ → ℝ} (hv : ∀ k, 0 ≤ v k) (a m : ℕ) :
    v m ≤ translate a v m := by
  rw [translate_split]
  exact le_add_of_nonneg_right (lower_nonneg (fun k _ => hv k) a)

private theorem moment_pos {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b)
    (hv : ComplementaryMomentRecurrence b d v) (j m : ℕ) : 0 < v j m := by
  induction j with
  | zero =>
    apply pos_of_residual (coeff_lt hb (omitted_lt hb) m) (moment_nonneg hb hv 0)
    rw [row_eq hb hv]
    change 0 < (b : ℝ) ^ (m + 1)
    have hb' : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    exact pow_pos hb' _
  | succ j ih =>
    apply pos_of_residual (coeff_lt hb (omitted_lt hb) m) (moment_nonneg hb hv _)
    rw [row_eq hb hv]
    exact ih.trans_le (translate_ge (moment_nonneg hb hv j) _ m)

private abbrev gap (v : ℕ → ℝ) (m : ℕ) := v m - v (m + 1)

private theorem translate_gap (a : ℕ) (v : ℕ → ℝ) (m : ℕ) :
    translate a (gap v) m = (1 + a) * translate a v m - translate a v (m + 1) := by
  change translate a (fun k => v k - v (k + 1)) m = _
  rw [translate_sub, translate_succ]
  ring

private theorem gap_residual_eq {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b)
    (hv : ComplementaryMomentRecurrence b d v) (j m : ℕ) :
    residual (digits b (omitted b d)) ((b : ℝ) ^ (m + 2)) (gap (v j)) m =
      b * forcing b d v j m - forcing b d v j (m + 1) +
        ∑ a ∈ digits b (omitted b d),
          ((b : ℝ) - 1 - a) * translate a (v j) m := by
  rw [← row_eq hb hv, ← row_eq hb hv]
  simp only [residual, translate_gap, sum_sub_distrib, gap, mul_sub, mul_sum]
  rw [pow_succ']
  simp only [sub_mul, add_mul, sum_sub_distrib, sum_add_distrib, one_mul]
  ring

private theorem digit_gap_nonneg {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b)
    (hv : ComplementaryMomentRecurrence b d v) (j m : ℕ) :
    0 ≤ ∑ a ∈ digits b (omitted b d),
      ((b : ℝ) - 1 - a) * translate a (v j) m := by
  refine sum_nonneg fun a ha => mul_nonneg ?_ (translate_nonneg (moment_nonneg hb hv j) a m)
  have ha' := mem_range.mp (mem_erase.mp ha).2
  have hr : (a : ℝ) + 1 ≤ b := by exact_mod_cast (by omega : a + 1 ≤ b)
  linarith

private theorem gap_residual_succ_ge {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b)
    (hv : ComplementaryMomentRecurrence b d v) (j m : ℕ) :
    translate (omitted b d) (gap (v j)) m ≤
      residual (digits b (omitted b d)) ((b : ℝ) ^ (m + 2)) (gap (v (j + 1))) m := by
  rw [gap_residual_eq hb hv, forcing, forcing, translate_gap]
  have hs := digit_gap_nonneg hb hv (j + 1) m
  have ht := translate_nonneg (moment_nonneg hb hv j) (omitted b d) m
  have he : (1 : ℝ) + omitted b d ≤ b := by
    exact_mod_cast (by have := omitted_lt (d := d) hb; omega : 1 + omitted b d ≤ b)
  nlinarith only [hs, ht, he]

private theorem gap_nonneg {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b)
    (hv : ComplementaryMomentRecurrence b d v) (j : ℕ) : ∀ m, 0 ≤ gap (v j) m := by
  induction j with
  | zero =>
    refine nonneg_of_residual (fun m => coeff_lt hb (omitted_lt (d := d) hb) (m + 1)) ?_
    intro m
    rw [gap_residual_eq hb hv]
    simpa [forcing, pow_succ'] using digit_gap_nonneg hb hv 0 m
  | succ j ih =>
    exact nonneg_of_residual (fun m => coeff_lt hb (omitted_lt hb) (m + 1))
      (fun m => (translate_nonneg ih _ m).trans (gap_residual_succ_ge hb hv j m))

private theorem exists_lower_digit {b d : ℕ} (hb : 1 < b) (hd : d < b)
    (he : ¬(b = 2 ∧ d = 1)) : ∃ a ∈ digits b (omitted b d), a + 1 < b := by
  by_cases h : omitted b d = 0
  · refine ⟨1, mem_erase.mpr ⟨by omega, mem_range.mpr hb⟩, ?_⟩
    dsimp [omitted] at h
    omega
  · exact ⟨0, mem_erase.mpr ⟨Ne.symm h, mem_range.mpr (by omega)⟩, hb⟩

private theorem digit_gap_pos {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b) (hd : d < b)
    (hv : ComplementaryMomentRecurrence b d v) (he : ¬(b = 2 ∧ d = 1)) (j m : ℕ) :
    0 < ∑ a ∈ digits b (omitted b d),
      ((b : ℝ) - 1 - a) * translate a (v j) m := by
  refine sum_pos' ?_ ?_
  · intro a ha
    have ha' := mem_range.mp (mem_erase.mp ha).2
    have hr : (a : ℝ) + 1 ≤ b := by exact_mod_cast (by omega : a + 1 ≤ b)
    exact mul_nonneg (by linarith) (translate_nonneg (moment_nonneg hb hv j) a m)
  · obtain ⟨a, ha, ha'⟩ := exists_lower_digit hb hd he
    have hr : (a : ℝ) + 1 < b := by exact_mod_cast ha'
    exact ⟨a, ha, mul_pos (by linarith)
      ((moment_pos hb hv j m).trans_le (translate_ge (moment_nonneg hb hv j) a m))⟩

private theorem gap_pos {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b) (hd : d < b)
    (hv : ComplementaryMomentRecurrence b d v) (j m : ℕ)
    (he : ¬(b = 2 ∧ d = 1 ∧ j = 0)) : 0 < gap (v j) m := by
  by_cases h : b = 2 ∧ d = 1
  · obtain ⟨rfl, rfl⟩ := h
    cases j with
    | zero => exact (he ⟨rfl, rfl, rfl⟩).elim
    | succ j =>
      apply pos_of_residual (coeff_lt hb (omitted_lt hb) (m + 1)) (gap_nonneg hb hv _)
      rw [gap_residual_eq hb hv]
      have hg := translate_nonneg (gap_nonneg hb hv j) 0 m
      have hp := moment_pos hb hv j m
      have hz (w : ℕ → ℝ) (k : ℕ) : translate 0 w k = w k := by
        simp [translate, sum_range_succ', pow_succ]
      simp only [hz] at hg
      change 0 ≤ v j m - v j (m + 1) at hg
      norm_num [forcing, omitted, digits, sum_range_succ, hz]
      linarith only [hg, hp]
  · cases j with
    | zero =>
      apply pos_of_residual (coeff_lt hb (omitted_lt hb) (m + 1)) (gap_nonneg hb hv 0)
      rw [gap_residual_eq hb hv]
      simpa [forcing, pow_succ'] using digit_gap_pos hb hd hv h 0 m
    | succ j =>
      apply pos_of_residual (coeff_lt hb (omitted_lt hb) (m + 1)) (gap_nonneg hb hv _)
      rw [gap_residual_eq hb hv]
      have hs := digit_gap_pos hb hd hv h (j + 1) m
      have hg := translate_nonneg (gap_nonneg hb hv j) (omitted b d) m
      have ht := translate_nonneg (moment_nonneg hb hv j) (omitted b d) m
      have he' : (1 : ℝ) + omitted b d ≤ b := by
        exact_mod_cast (by have := omitted_lt (d := d) hb; omega : 1 + omitted b d ≤ b)
      simp only [forcing]
      rw [translate_gap] at hg
      nlinarith only [hs, hg, ht, he']

private theorem moment_le_base {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b)
    (hv : ComplementaryMomentRecurrence b d v) (j m : ℕ) : v j m ≤ b := by
  have ha : Antitone (v j) :=
    antitone_nat_of_succ_le fun n => sub_nonneg.mp (gap_nonneg hb hv j n)
  exact (ha (Nat.zero_le m)).trans_eq (degree_zero hv j)

private theorem translate_const (a m : ℕ) (c : ℝ) :
    translate a (fun _ => c) m = c * ((a : ℝ) + 1) ^ m := by
  have hp : ((a : ℝ) + 1) ^ m =
      ∑ i ∈ range (m + 1), (m.choose i : ℝ) * (a : ℝ) ^ i := by
    rw [add_pow]
    simp [mul_comm]
  rw [hp, mul_sum]
  exact sum_congr rfl fun i _ => by ring

private theorem exceptional_zero {v : ℕ → ℕ → ℝ}
    (hv : ComplementaryMomentRecurrence 2 1 v) (m : ℕ) : v 0 m = 2 := by
  have hc (k : ℕ) : ((digits 2 0).card : ℝ) < (2 : ℝ) ^ (k + 1) := by
    simpa using coeff_lt (b := 2) (d := 0) (by decide) (by decide) k
  have hr (k : ℕ) : residual (digits 2 0) ((2 : ℝ) ^ (k + 1)) (fun _ => 2) k =
      (2 : ℝ) ^ (k + 1) := by
    norm_num [residual, digits, sum_range_succ, translate_const, pow_succ]
    ring
  have he (k : ℕ) : residual (digits 2 0) ((2 : ℝ) ^ (k + 1)) (v 0) k =
      residual (digits 2 0) ((2 : ℝ) ^ (k + 1)) (fun _ => 2) k := by
    rw [hr]
    simpa [forcing, omitted] using row_eq (by decide : 1 < 2) hv 0 k
  have h₁ : ∀ k, 0 ≤ v 0 k - 2 := nonneg_of_residual hc (fun k => by
    rw [residual_sub, he]
    exact sub_self _ |>.ge)
  have h₂ : ∀ k, 0 ≤ 2 - v 0 k := nonneg_of_residual hc (fun k => by
    rw [residual_sub, he]
    exact sub_self _ |>.ge)
  exact le_antisymm (sub_nonneg.mp (h₂ m)) (sub_nonneg.mp (h₁ m))

private theorem translate_le_const {v : ℕ → ℝ} {c : ℝ} (hv : ∀ k, v k ≤ c) (a m : ℕ) :
    translate a v m ≤ c * ((a : ℝ) + 1) ^ m := by
  rw [← translate_const]
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv _) (by positivity)

private theorem translate_lt_const {v : ℕ → ℝ} {c : ℝ} (hv : ∀ k, v k ≤ c)
    (a m : ℕ) (hm : v m < c) : translate a v m < c * ((a : ℝ) + 1) ^ m := by
  rw [← translate_const]
  apply sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hv _) (by positivity))
  exact ⟨0, by simp, by simpa using hm⟩

private theorem decreasing {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b) (hd : d < b)
    (hv : ComplementaryMomentRecurrence b d v) (j : ℕ) :
    ∀ m, 1 ≤ m → v (j + 1) m < v j m := by
  have lift (n : ℕ) (hs : ∀ m, 1 ≤ m → forcing b d v (n + 1) m < forcing b d v n m) :
      ∀ m, 1 ≤ m → v (n + 1) m < v n m := by
    let w := fun k => v n k - v (n + 1) k
    have step (m : ℕ) (hm : 1 ≤ m) :
        0 < residual (digits b (omitted b d)) ((b : ℝ) ^ (m + 1)) w m := by
      dsimp [w]
      rw [residual_sub, row_eq hb hv, row_eq hb hv]
      exact sub_pos.mpr (hs m hm)
    have hn : ∀ m, 0 ≤ w m := nonneg_of_residual (coeff_lt hb (omitted_lt hb)) (fun m => by
      cases m with
      | zero => simp [w, residual, translate, degree_zero hv]
      | succ m => exact (step _ (by omega)).le)
    exact fun m hm => sub_pos.mp
      (pos_of_residual (coeff_lt hb (omitted_lt hb) m) hn (step m hm))
  induction j with
  | zero =>
    apply lift
    intro m hm
    change translate (omitted b d) (v 0) m < (b : ℝ) ^ (m + 1)
    have hb' : 0 < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    have he : (omitted b d : ℝ) + 1 ≤ b := by
      exact_mod_cast (by have := omitted_lt (d := d) hb; omega : omitted b d + 1 ≤ b)
    have hp : (b : ℝ) * ((omitted b d : ℝ) + 1) ^ m ≤ (b : ℝ) ^ (m + 1) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) he m) hb'.le
    by_cases h : (omitted b d : ℝ) + 1 < b
    · have ht := translate_le_const (moment_le_base hb hv 0) (omitted b d) m
      have hp' : ((omitted b d : ℝ) + 1) ^ m < (b : ℝ) ^ m :=
        pow_lt_pow_left₀ h (by positivity) (by omega)
      exact ht.trans_lt (by rw [pow_succ']; exact mul_lt_mul_of_pos_left hp' hb')
    · have hd0 : d = 0 := by
        have he' : omitted b d + 1 = b := by exact_mod_cast (le_antisymm he (le_of_not_gt h))
        dsimp [omitted] at he'
        omega
      have hg := gap_pos hb hd hv 0 0 (by omega)
      have ha : Antitone (v 0) :=
        antitone_nat_of_succ_le fun k => sub_nonneg.mp (gap_nonneg hb hv 0 k)
      have hvlt : v 0 m < b := (ha hm).trans_lt (by
        have hz := degree_zero hv 0
        change 0 < v 0 0 - v 0 1 at hg
        linarith only [hg, hz])
      exact (translate_lt_const (moment_le_base hb hv 0) _ _ hvlt).trans_le hp
  | succ j ih =>
    apply lift
    intro m hm
    apply sub_pos.mp
    change 0 < translate (omitted b d) (v j) m - translate (omitted b d) (v (j + 1)) m
    rw [← translate_sub]
    refine (sub_pos.mpr (ih m hm)).trans_le (translate_ge (v := fun k =>
      v j k - v (j + 1) k) ?_ _ m)
    intro k
    cases k with
    | zero => simp [degree_zero hv]
    | succ k => exact (sub_pos.mpr (ih _ (by omega))).le

private noncomputable abbrev uniformMoment (b m : ℕ) : ℝ := b / ((m : ℝ) + 1)

private theorem translate_uniform (b a m : ℕ) :
    translate a (uniformMoment b) m =
      uniformMoment b m * (((a : ℝ) + 1) ^ (m + 1) - (a : ℝ) ^ (m + 1)) := by
  have hpow : ((a : ℝ) + 1) ^ (m + 1) - (a : ℝ) ^ (m + 1) =
      ∑ i ∈ range (m + 1), (a : ℝ) ^ i * (m + 1).choose i := by
    rw [add_pow, sum_range_succ]
    simp
  rw [hpow, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  have h := Nat.choose_mul_succ_eq m i
  have hi : m + 1 - i = (m - i) + 1 := by omega
  rw [hi] at h
  have hr : (m.choose i : ℝ) * (m + 1) = ((m + 1).choose i : ℝ) * ((m - i : ℕ) + 1) := by
    exact_mod_cast h
  dsimp [uniformMoment]
  field_simp
  linear_combination (a : ℝ) ^ i * b * hr

private theorem uniform_stationary (b m : ℕ) :
    residual (range b) ((b : ℝ) ^ (m + 1)) (uniformMoment b) m = 0 := by
  simp only [residual, translate_uniform, ← mul_sum]
  have ht := sum_range_sub (fun n : ℕ => (n : ℝ) ^ (m + 1)) b
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_pow (Nat.succ_ne_zero _),
    sub_zero] at ht
  rw [ht]
  ring

private theorem translate_tendsto {v : ℕ → ℕ → ℝ} {l : ℕ → ℝ}
    (hl : ∀ m, Tendsto (fun j => v j m) atTop (nhds (l m))) (a m : ℕ) :
    Tendsto (fun j => translate a (v j) m) atTop (nhds (translate a l m)) :=
  tendsto_finsetSum _ fun i _ => (hl (m - i)).const_mul _

private theorem limit_stationary {b d : ℕ} {v : ℕ → ℕ → ℝ}
    (hb : 1 < b) (hv : ComplementaryMomentRecurrence b d v)
    {l : ℕ → ℝ} (hl : ∀ m, Tendsto (fun j => v j m) atTop (nhds (l m))) (m : ℕ) :
    residual (range b) ((b : ℝ) ^ (m + 1)) l m = 0 := by
  have hs (k : ℕ) := (tendsto_add_atTop_iff_nat 1).mpr (hl k)
  have h : residual (digits b (omitted b d)) ((b : ℝ) ^ (m + 1)) l m =
      translate (omitted b d) l m := by
    refine tendsto_nhds_unique_of_eventuallyEq
      (((hs m).const_mul _).sub (tendsto_finsetSum _ fun a _ => translate_tendsto hs a m))
      (translate_tendsto hl (omitted b d) m) ?_
    exact Eventually.of_forall fun j => row_eq hb hv (j + 1) m
  rw [residual, ← (range b).sum_erase_add (fun a => translate a l m)
    (mem_range.mpr (omitted_lt (d := d) hb))]
  unfold residual at h
  linarith

private theorem limit_eq_uniform {b : ℕ} (hb : 1 < b) {l : ℕ → ℝ} (h0 : l 0 = b)
    (hl : ∀ m, residual (range b) ((b : ℝ) ^ (m + 1)) l m = 0) :
    ∀ m, l m = uniformMoment b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rcases m with _ | m
    · simpa [uniformMoment] using h0
    · have he := hl (m + 1)
      have hu := uniform_stationary b (m + 1)
      have heq (a : ℕ) : lower a l (m + 1) = lower a (uniformMoment b) (m + 1) := by
        refine sum_congr rfl fun i hi => ?_
        rw [ih _ (by have := mem_Icc.mp hi; omega)]
      simp only [residual_eq, card_range, heq] at he hu
      have hp : (b : ℝ) ^ 1 < (b : ℝ) ^ (m + 1 + 1) :=
        pow_lt_pow_right₀ (by exact_mod_cast hb) (by omega)
      rw [pow_one] at hp
      apply mul_left_cancel₀ (sub_ne_zero.mpr hp.ne')
      linarith only [he, hu]

private theorem moment_tendsto {b d : ℕ} {v : ℕ → ℕ → ℝ} (hb : 1 < b) (hd : d < b)
    (hv : ComplementaryMomentRecurrence b d v) (m : ℕ) :
    Tendsto (fun j => v j m) atTop (nhds (uniformMoment b m)) := by
  let l (k : ℕ) := ⨅ j, v j k
  have hl (k : ℕ) : Tendsto (fun j => v j k) atTop (nhds (l k)) := by
    apply tendsto_atTop_ciInf
    · apply antitone_nat_of_succ_le
      intro j
      cases k with
      | zero => simp [degree_zero hv]
      | succ k => exact (decreasing hb hd hv j _ (by omega)).le
    · refine ⟨0, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact moment_nonneg hb hv j k
  have h0 : l 0 = b :=
    tendsto_nhds_unique_of_eventuallyEq (hl 0) tendsto_const_nhds
      (Eventually.of_forall (degree_zero hv))
  rw [← limit_eq_uniform hb h0 (limit_stationary hb hv hl) m]
  exact hl m

end complementaryMomentRecurrence_properties

open complementaryMomentRecurrence_properties

/-- **Properties of the complementary moment recurrence.** Let $b > 1$ and $d < b$ be natural
numbers, and let $(v_{j,m})_{j, m \ge 0}$ be any family of real numbers satisfying the
complementary moment recurrence for $b$ and $d$. Then $v_{j,0} = b$ for every $j$. For every $j$
and every $m \ge 1$: $0 < v_{j,m} \le b$; if $(b, d, j) = (2, 1, 0)$ then $v_{j,m} = 2$, and
otherwise $v_{j,m+1} < v_{j,m}$; and $v_{j+1,m} < v_{j,m}$. Finally, for every $m \ge 1$,
$v_{j,m} \to b/(m+1)$ as $j \to \infty$.

Source: Jean-François
Burnol, *Measures for the Summation of Irwin Series*, INTEGERS 26 (2026),
Article A11, Theorem 2. -/
public theorem complementaryMomentRecurrence_properties
    (b d : ℕ) (hb : 1 < b) (hd : d < b) (v : ℕ → ℕ → ℝ)
    (hv : ComplementaryMomentRecurrence b d v) :
    (∀ j, v j 0 = b) ∧
    (∀ j m, 1 ≤ m → 0 < v j m ∧ v j m ≤ b) ∧
    (∀ j m, 1 ≤ m →
      ((b = 2 ∧ d = 1 ∧ j = 0) → v j m = 2) ∧
      (¬(b = 2 ∧ d = 1 ∧ j = 0) → v j (m + 1) < v j m)) ∧
    (∀ j m, 1 ≤ m → v (j + 1) m < v j m) ∧
    (∀ m, 1 ≤ m →
      Tendsto (fun j : ℕ => v j m) atTop (nhds ((b : ℝ) / (m + 1)))) := by
  exact ⟨degree_zero hv, fun j m _ => ⟨moment_pos hb hv j m, moment_le_base hb hv j m⟩,
    fun j m _ => ⟨fun he => by
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact exceptional_zero hv m,
      fun he => sub_pos.mp (gap_pos hb hd hv j m he)⟩,
    decreasing hb hd hv, fun m _ => moment_tendsto hb hd hv m⟩

end MetaMathlibExt
