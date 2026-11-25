/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/729.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definition of `conjecture` and the statement of `conjecture_holds`.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Rat.Init
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Smooth denominators of factorial ratios

`conjecture_holds` proves Erdős Problem 729. We use triples `(a, a + k, 2 * a)`.
Digits in the middle of the upper half of a base-`p` expansion give surplus factors
of `p` in the factorial ratio. A finite counting argument supplies enough such digits
simultaneously in all the bases that need them.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem729Wanted

/-- **Erdős Problem 729.** The proposition that for every real number $C > 0$ there is a natural
number $K \ge 3$ such that there are infinitely many triples $(a, b, n)$ of positive integers with
$a + b > n + C \log n$ for which no prime $p > K$ divides the denominator of the rational number
$n! / (a! \, b!)$ in lowest terms. -/
def conjecture : Prop :=
  ∀ (C : ℝ) (_ : C > 0),
    ∃ K ≥ 3, Set.Infinite {T : ℕ × ℕ × ℕ |
      let (a, b, n) := T
      a > 0 ∧ b > 0 ∧ n > 0 ∧
      (a : ℝ) + b > n + C * Real.log n ∧
      ∀ p, p.Prime → p > K →
        padicValNat p ((n.factorial / (a.factorial * b.factorial) : ℚ).den) = 0}

open Finset

/-- Digits in this interval force a carry on doubling, with room for a shift. -/
private def middle (p : ℕ) : Finset ℕ := Ico ((p + 1) / 2) (3 * p / 4)

private def hit (p x i : ℕ) : ℕ :=
  if x / p ^ i % p ∈ middle p then 1 else 0

private def hits (p x d : ℕ) : ℕ := ∑ i ∈ range d, hit p x i

private lemma floor_bound {x k q : ℕ} (hq : 0 < q) :
    x / q + (x + k) / q ≤ (2 * x) / q + (2 * k) / q := by
  let r := x % q
  have hx : x = q * (x / q) + r := (Nat.div_add_mod x q).symm
  have h₁ : (x + k) / q = x / q + (r + k) / q := by
    conv_lhs => rw [hx, Nat.add_assoc, Nat.mul_add_div hq]
  have h₂ : (2 * x) / q = 2 * (x / q) + (2 * r) / q := by
    conv_lhs => rw [hx, Nat.mul_add, Nat.mul_left_comm, Nat.mul_add_div hq]
  rw [h₁, h₂]
  have := Nat.zero_le (2 * k / q)
  have := Nat.zero_le (2 * r / q)
  rcases le_total r k with h | h
  · have := Nat.div_le_div_right (show r + k ≤ 2 * k by omega) (c := q)
    omega
  · have := Nat.div_le_div_right (show r + k ≤ 2 * r by omega) (c := q)
    omega

private lemma floor_hit {p x k i : ℕ} (hp : 0 < p) :
    x / p ^ (i + 1) + (x + k) / p ^ (i + 1) + hit p x i ≤
      (2 * x) / p ^ (i + 1) + (8 * k) / p ^ (i + 1) := by
  let u := p ^ i
  let q := p ^ (i + 1)
  have hu : 0 < u := pow_pos hp _
  have hq : 0 < q := pow_pos hp _
  have hbase := floor_bound (x := x) (k := k) hq
  change x / q + (x + k) / q + _ ≤ (2 * x) / q + (8 * k) / q
  unfold hit
  split_ifs with h
  · by_cases hsmall : q ≤ 4 * k
    · have hinc : (2 * k) / q + 1 ≤ (8 * k) / q := by
        rw [Nat.le_div_iff_mul_le hq, Nat.add_mul, one_mul]
        have := Nat.div_mul_le_self (2 * k) q
        omega
      omega
    · have hd := mem_Ico.mp h
      have hr := Nat.mod_lt x hu
      have he : x % q = x % u + u * (x / u % p) := by
        dsimp [q, u]
        rw [pow_succ, Nat.mod_mul]
      have hqu : q = u * p := pow_succ _ _
      change (p + 1) / 2 ≤ x / u % p ∧ x / u % p < 3 * p / 4 at hd
      have hlo : p ≤ 2 * (x / u % p) := by omega
      have hhi : 4 * (x / u % p + 1) ≤ 3 * p := by omega
      have hl : q ≤ 2 * (x % q) := by
        rw [he, hqu]
        nlinarith [Nat.mul_le_mul_left u hlo, Nat.zero_le (x % u)]
      have hh : 4 * (x % q) < 3 * q := by
        have := Nat.mul_le_mul_left u hhi
        nlinarith
      have hdiv : (x + k) / q = x / q := by
        conv_lhs => rw [← Nat.div_add_mod x q, Nat.add_assoc, Nat.mul_add_div hq,
          Nat.div_eq_of_lt (show x % q + k < q by omega), Nat.add_zero]
      have hdouble : 2 * (x / q) + 1 ≤ 2 * x / q := by
        rw [Nat.le_div_iff_mul_le hq, Nat.add_mul, one_mul]
        have := Nat.div_add_mod x q
        nlinarith
      rw [hdiv, ← two_mul]
      exact hdouble.trans (Nat.le_add_right _ _)
  · have := Nat.div_le_div_right (show 2 * k ≤ 8 * k by omega) (c := q)
    omega

private lemma factorial_bound {p : ℕ} (hp : p.Prime) (x k d : ℕ) :
    x.factorial.factorization p + (x + k).factorial.factorization p + hits p x d ≤
      (2 * x).factorial.factorization p + (8 * k).factorial.factorization p := by
  let B := d + 2 * x + 8 * k + 1
  have leg (m : ℕ) (hm : m < B) :
      m.factorial.factorization p = ∑ i ∈ range B, m / p ^ (i + 1) := by
    rw [Nat.factorization_factorial hp ((Nat.log_le_self p m).trans_lt (Nat.lt_succ_of_lt hm))]
    simpa using (sum_Ico_add' (fun i => m / p ^ i) 0 B 1).symm
  have h := sum_le_sum (fun i (_ : i ∈ range B) => floor_hit (x := x) (k := k) (i := i) hp.pos)
  simp only [sum_add_distrib] at h
  have hsub : hits p x d ≤ ∑ i ∈ range B, hit p x i :=
    sum_le_sum_of_subset (range_mono (by dsimp [B]; omega))
  rw [leg x (by dsimp [B]; omega), leg (x + k) (by dsimp [B]; omega),
    leg (2 * x) (by dsimp [B]; omega), leg (8 * k) (by dsimp [B]; omega)]
  omega

private lemma den_val_zero {p A B : ℕ} (hp : p.Prime) (hA : A ≠ 0) (hB : B ≠ 0)
    (h : B.factorization p ≤ A.factorization p) : padicValNat p ((A : ℚ) / B).den = 0 := by
  have he : (A : ℚ) / B = mkRat A B := (Rat.mkRat_eq_div A B).symm
  rw [he, Rat.den_mkRat, ite_eq_right hB, Int.natAbs_natCast, Nat.padicValNat_def,
    ← Nat.factorization_def _ hp, Nat.factorization_div (Nat.gcd_dvd_left B A),
    Nat.factorization_gcd hB hA]
  simp [Finsupp.inf_apply, min_eq_left h]

/-- Splitting a finite interval into consecutive blocks of length `p`. -/
private lemma sum_blocks (f : ℕ → ℝ) (p n : ℕ) :
    ∑ x ∈ range (p * n), f x = ∑ a ∈ range n, ∑ b ∈ range p, f (p * a + b) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

private lemma hits_succ (p x d : ℕ) :
    hits p x (d + 1) = hits p (x / p) d + (if x % p ∈ middle p then 1 else 0) := by
  unfold hits
  rw [sum_range_succ']
  simp only [hit, pow_zero, Nat.div_one, Nat.div_div_eq_div_mul, pow_succ']

private lemma digit_weight {p : ℕ} (hp : 16 ≤ p) :
    ∑ b ∈ range p, ((1 / 2 : ℝ) ^ (if b ∈ middle p then 1 else 0 : ℕ)) ≤ p * (15 / 16) := by
  have hsub : middle p ⊆ range p := by
    intro b hb
    have := (mem_Ico.mp hb).2
    simp only [mem_range]
    omega
  have he (b : ℕ) : (1 / 2 : ℝ) ^ (if b ∈ middle p then 1 else 0 : ℕ) =
      1 - (if b ∈ middle p then 1 / 2 else 0) := by split_ifs <;> norm_num
  simp_rw [he]
  rw [sum_sub_distrib, ← sum_filter]
  have hf : (range p).filter (· ∈ middle p) = middle p := by
    ext b
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun hb => hsub hb
  rw [hf]
  have hc : p ≤ 8 * (middle p).card := by
    simp only [middle, Nat.card_Ico]
    omega
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  linarith [show (p : ℝ) ≤ 8 * (middle p).card by exact_mod_cast hc]

/-- The weight of each number is halved at each hit. Summing over the last digit
contracts the total weight by a factor at most `15 / 16` relative to the length. -/
private lemma weight_sum {p : ℕ} (hp : 16 ≤ p) (m d : ℕ) :
    ∑ x ∈ range (m * p ^ d), (1 / 2 : ℝ) ^ hits p x d ≤
      (m : ℝ) * (p * (15 / 16) : ℝ) ^ d := by
  have hp₀ : 0 < p := by omega
  induction d with
  | zero => simp [hits]
  | succ d ih =>
    rw [show m * p ^ (d + 1) = p * (m * p ^ d) by rw [pow_succ]; ring, sum_blocks]
    calc
      _ = ∑ a ∈ range (m * p ^ d), (1 / 2 : ℝ) ^ hits p a d *
          ∑ b ∈ range p, (1 / 2 : ℝ) ^ (if b ∈ middle p then 1 else 0 : ℕ) := by
        apply sum_congr rfl
        intro a _
        rw [mul_sum]
        apply sum_congr rfl
        intro b hb
        have hb' := mem_range.mp hb
        simp [hits_succ, Nat.mul_add_div hp₀, Nat.div_eq_of_lt hb',
          Nat.mod_eq_of_lt hb', pow_add]
      _ ≤ (∑ a ∈ range (m * p ^ d), (1 / 2 : ℝ) ^ hits p a d) * (p * (15 / 16)) := by
        rw [sum_mul]
        exact sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (digit_weight hp) (by positivity)
      _ ≤ _ := by
        rw [pow_succ, ← mul_assoc (m : ℝ)]
        exact mul_le_mul_of_nonneg_right ih (by positivity)

private def exceptions (p N s : ℕ) : Finset ℕ :=
  (range N).filter fun x => hits p x (32 * s) < s

/-- At most a proportion `2 / 2^s` can have fewer than `s` hits in `32*s` digits. -/
private lemma exceptions_bound {p N s : ℕ} (hp : 16 ≤ p) (hperiod : p ^ (32 * s) ≤ N) :
    ((exceptions p N s).card : ℝ) * 2 ^ s ≤ 2 * N := by
  let d := 32 * s
  let m := N / p ^ d + 1
  have hpow : 0 < p ^ d := pow_pos (by omega) _
  have hcover : N ≤ m * p ^ d := by
    dsimp [m]
    rw [Nat.add_mul, one_mul]
    have := Nat.div_add_mod N (p ^ d)
    have := Nat.mod_lt N hpow
    rw [Nat.mul_comm (N / p ^ d)]
    omega
  have hlen : m * p ^ d ≤ 2 * N := by
    dsimp [m]
    rw [Nat.add_mul, one_mul]
    have := Nat.div_mul_le_self N (p ^ d)
    change p ^ d ≤ N at hperiod
    omega
  have sub : exceptions p N s ⊆ range (m * p ^ d) :=
    (filter_subset _ _).trans (range_mono hcover)
  have hw : (15 / 16 : ℝ) ^ d * 4 ^ s ≤ 1 := by
    dsimp [d]
    rw [pow_mul, ← mul_pow]
    exact pow_le_one₀ (by positivity) (by norm_num)
  calc
    _ = ∑ x ∈ exceptions p N s, (2 : ℝ) ^ s := by simp
    _ ≤ ∑ x ∈ exceptions p N s, (1 / 2 : ℝ) ^ hits p x d * 4 ^ s := by
      apply sum_le_sum
      intro x hx
      have hx' : hits p x d ≤ s := (mem_filter.mp hx).2.le
      calc
        _ = (1 / 2 : ℝ) ^ s * 4 ^ s := by rw [← mul_pow]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hx') (by positivity)
    _ ≤ (∑ x ∈ range (m * p ^ d), (1 / 2 : ℝ) ^ hits p x d) * 4 ^ s := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sum_le_sum_of_subset_of_nonneg sub fun _ _ _ => by positivity) (by positivity)
    _ ≤ (m : ℝ) * (p * (15 / 16) : ℝ) ^ d * 4 ^ s := by
      gcongr
      exact weight_sum hp m d
    _ = (m * p ^ d : ℕ) * ((15 / 16 : ℝ) ^ d * 4 ^ s) := by push_cast; rw [mul_pow]; ring
    _ ≤ (m * p ^ d : ℕ) * (1 : ℝ) := by gcongr
    _ ≤ _ := by rw [mul_one]; exact_mod_cast hlen

/-- A union bound over the relevant bases; zero is discarded as well. -/
private lemma simultaneous {N J K t : ℕ} (s : ℕ → ℕ) (hN : 2 < N)
    (hcount : 4 * (J + 1) ≤ 2 ^ t)
    (hbase : ∀ p, K < p → p ≤ J → 16 ≤ p ∧ t ≤ s p ∧ p ^ (32 * s p) ≤ N) :
    ∃ x, 0 < x ∧ x < N ∧ ∀ p, K < p → p ≤ J → s p ≤ hits p x (32 * s p) := by
  let bases := (range (J + 1)).filter (K < ·)
  let bad := bases.biUnion fun p => exceptions p N (s p)
  have he (p : ℕ) (hp : p ∈ bases) : (exceptions p N (s p)).card * 2 ^ t ≤ 2 * N := by
    obtain ⟨hle, ht, hper⟩ := hbase p (mem_filter.mp hp).2
      (Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hp).1))
    have h : (exceptions p N (s p)).card * 2 ^ s p ≤ 2 * N := by
      exact_mod_cast exceptions_bound hle hper
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) ht)).trans h
  have hcard : bad.card * 2 ^ t ≤ (J + 1) * (2 * N) := calc
    _ ≤ (∑ p ∈ bases, (exceptions p N (s p)).card) * 2 ^ t :=
      Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ p ∈ bases, (exceptions p N (s p)).card * 2 ^ t := sum_mul ..
    _ ≤ ∑ _p ∈ bases, 2 * N := sum_le_sum he
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ ((card_filter_le ..).trans_eq (card_range _))
  have hhalf : 2 * bad.card ≤ N := by
    apply Nat.le_of_mul_le_mul_right (c := 2 ^ t) _ (by positivity)
    calc
      _ = 2 * (bad.card * 2 ^ t) := by ring
      _ ≤ 2 * ((J + 1) * (2 * N)) := Nat.mul_le_mul_left _ hcard
      _ = N * (4 * (J + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hcount
  have hins := card_insert_le 0 bad
  obtain ⟨x, hx, hx'⟩ := exists_mem_notMem_of_card_lt_card
    (s := insert 0 bad) (t := range N) (by rw [card_range]; omega)
  refine ⟨x, Nat.pos_of_ne_zero (fun h => hx' (h ▸ mem_insert_self ..)), mem_range.mp hx, ?_⟩
  intro p hp hpJ
  by_contra! h
  exact hx' (mem_insert_of_mem (mem_biUnion.mpr
    ⟨p, mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩, mem_filter.mpr ⟨hx, h⟩⟩))

private lemma square_le_exp {u : ℕ} (hu : 40 ≤ u) : 1024 * (u + 4) ^ 2 ≤ 2 ^ u := by
  induction u, hu using Nat.le_induction with
  | base => decide
  | succ u _ ih => rw [pow_succ 2]; nlinarith

/-- The cutoff makes the number of digits needed to cover the factorial loss affordable:
`32 * (8*k/(p-1))` base-`p` digits take at most half of the binary digit budget. -/
private lemma period_bound {L m t p : ℕ} (hL : 0 < L) (hp : 2 ^ (L + 40) < p)
    (hslack : 64 * (Nat.log 2 p + 1) * t ≤ m) :
    p ^ (32 * (8 * (L * m) / (p - 1) + t)) ≤ 2 ^ m := by
  let e := Nat.log 2 p + 1
  have hu : L + 40 ≤ Nat.log 2 p := Nat.le_log_of_pow_le (by decide) hp.le
  have hsq := square_le_exp (u := Nat.log 2 p) (by omega)
  have hp₀ : 0 < p := (Nat.zero_le _).trans_lt hp
  have hpow := Nat.pow_log_le_self 2 hp₀.ne'
  have hcut : 512 * L * e ≤ p - 1 := by
    dsimp [e]
    have := Nat.mul_le_mul_right (Nat.log 2 p + 1) (show L ≤ Nat.log 2 p by omega)
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ p)]
  let loss := 8 * (L * m) / (p - 1)
  have hprod : loss * (512 * L * e) ≤ 8 * (L * m) :=
    (Nat.mul_le_mul_left loss hcut).trans (Nat.div_mul_le_self _ _)
  have hcost : 64 * e * loss ≤ m := by
    apply Nat.le_of_mul_le_mul_right (c := 8 * L) _ (by positivity)
    calc
      _ = loss * (512 * L * e) := by ring
      _ ≤ _ := hprod.trans_eq (by ring)
  change 64 * e * t ≤ m at hslack
  change p ^ (32 * (loss + t)) ≤ _
  calc
    _ ≤ (2 ^ e) ^ (32 * (loss + t)) :=
      Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by decide : 1 < 2) p).le _
    _ = 2 ^ (e * (32 * (loss + t))) := (pow_mul ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

private lemma log_growth {x m L : ℕ} (hL : 0 < L) (hx : 0 < x) (hxm : x ≤ 2 ^ m)
    (hm : 1 < m) : (L : ℝ) * Real.log (2 * x) < 2 * (L * m : ℕ) := by
  have hpow : (2 * x : ℝ) ≤ 2 ^ (m + 1) := by
    rw [pow_succ]
    linarith only [show (x : ℝ) ≤ (2 : ℝ) ^ m by exact_mod_cast hxm]
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Nat.cast_succ] at hlog
  have hlog₂ : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlt : Real.log (2 * x) < 2 * m := by
    linarith only [hlog, mul_le_mul_of_nonneg_left hlog₂ (show (0 : ℝ) ≤ m + 1 by positivity),
      (show (1 : ℝ) < m by exact_mod_cast hm)]
  push_cast
  linarith only [mul_lt_mul_of_pos_left hlt (show (0 : ℝ) < L by exact_mod_cast hL)]

private lemma witnesses (L B : ℕ) (hL : 0 < L) :
    ∃ x k : ℕ, 0 < x ∧ B < x + k ∧
      (L : ℝ) * Real.log (2 * x) < 2 * k ∧
      ∀ p, p.Prime → 2 ^ (L + 40) < p →
        x.factorial.factorization p + (x + k).factorial.factorization p ≤
          (2 * x).factorial.factorization p := by
  let u := B + 8 * L + 40
  let m := 2 ^ u
  let N := 2 ^ m
  let k := L * m
  let t := 2 * u + 4
  let s (p : ℕ) := 8 * k / (p - 1) + t
  have hum : u < m := Nat.lt_two_pow_self
  have hmN : m < N := Nat.lt_two_pow_self
  have hu : 40 ≤ u := by dsimp [u]; omega
  have hLm : 8 * L ≤ m := by dsimp [u] at hum; omega
  have hJ : 8 * k ≤ 2 ^ (2 * u) := calc
    _ = 8 * L * m := by dsimp [k]; ring
    _ ≤ m * m := Nat.mul_le_mul_right _ hLm
    _ = _ := by simp [m, two_mul, pow_add]
  have hcount : 4 * (8 * k + 1) ≤ 2 ^ t := by
    dsimp [t]
    rw [pow_add]
    have : 0 < 2 ^ (2 * u) := by positivity
    omega
  obtain ⟨x, hx, hxN, hxgood⟩ := simultaneous (K := 2 ^ (L + 40)) s (by omega : 2 < N)
    hcount (by
      intro p hp hpJ
      have h16 : 16 ≤ 2 ^ (L + 40) := by
        exact Nat.pow_le_pow_right (n := 2) (by decide) (show 4 ≤ L + 40 by omega)
      refine ⟨h16.trans hp.le, Nat.le_add_left _ _, period_bound hL hp ?_⟩
      have he := Nat.log_mono_right (b := 2) (hpJ.trans hJ)
      rw [Nat.log_pow (by decide)] at he
      have hsq := square_le_exp hu
      dsimp [m, t]
      nlinarith [Nat.mul_le_mul_right (2 * u + 4) (show Nat.log 2 p + 1 ≤ 2 * u + 1 by omega)])
  refine ⟨x, k, hx, ?_, ?_, ?_⟩
  · have : m ≤ k := Nat.le_mul_of_pos_left _ hL
    dsimp [u] at hum
    omega
  · exact log_growth hL hx hxN.le (by omega : 1 < m)
  · intro p hp hK
    by_cases hpJ : p ≤ 8 * k
    · have hh := hxgood p hK hpJ
      have hval := Nat.factorization_factorial_le_div_pred hp (8 * k)
      have hsum := factorial_bound hp x k (32 * s p)
      have := (Nat.le_add_right (8 * k / (p - 1)) t).trans hh
      omega
    · have hsum := factorial_bound hp x k 0
      simpa [hits, Nat.factorization_factorial_eq_zero_of_lt (Nat.lt_of_not_ge hpJ)] using hsum

/--
**Erdős Problem 729 holds.** For every real number $C > 0$ there is a natural number $K \ge 3$
such that there are infinitely many triples $(a, b, n)$ of positive integers with
$a + b > n + C \log n$ for which no prime $p > K$ divides the denominator of the rational number
$n! / (a! \, b!)$ in lowest terms.

The statement was resolved in the affirmative by Barreto and Leeham.

Source: External Lean proof
of Erdős Problem 729,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos729.lean.
Moved from `OpenConjectures/NumberTheory/ErdosProblem729`.
-/
theorem conjecture_holds : conjecture := by
  intro C hC
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * C)
  have hL₀ : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  refine ⟨2 ^ (L + 40), ?_, ?_⟩
  · exact (by decide : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  · intro hfinite
    obtain ⟨B, hB⟩ := (hfinite.image (fun T : ℕ × ℕ × ℕ => T.2.1)).bddAbove
    obtain ⟨x, k, hx, hg, hlog, hv⟩ := witnesses L B hL₀
    apply hg.not_ge
    apply hB
    refine ⟨(x, x + k, 2 * x), ⟨hx, by omega, by omega, ?_, ?_⟩, rfl⟩
    · have hpos : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ 2 * x by omega))
      push_cast
      linarith [mul_le_mul_of_nonneg_right hL.le hpos]
    · intro p hp hK
      rw [← Nat.cast_mul]
      apply den_val_zero hp (Nat.factorial_ne_zero _) (by positivity)
      simpa [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
        using hv p hp hK

end MathlibExt.NumberTheory.ErdosProblem729Wanted
