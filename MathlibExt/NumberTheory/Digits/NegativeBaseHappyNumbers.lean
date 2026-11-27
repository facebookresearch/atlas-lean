/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Logic.Function.Iterate
public import MathlibExt.NumberTheory.Digits.NegativeBaseDigitSquareCongruence
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Negative base happy numbers

We prove that a common iterate of the negative-base digit-square map falls below twice the
squared base.

Statements from Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The
Fibonacci Quarterly 62 (2024), no. 2, 125–129.
-/

namespace MetaMathlibExt

private theorem aux_nonneg (b : ℤ) (f : ℕ) (a : ℤ) :
    0 ≤ negBaseSqDigitSumAux b f a := by
  induction f generalizing a with
  | zero => simp [negBaseSqDigitSumAux]
  | succ f ih =>
    unfold negBaseSqDigitSumAux
    split
    · omega
    · have h1 : 0 ≤ (a % b) ^ 2 := by nlinarith [sq_nonneg (a % b)]
      have h2 := ih ((a - a % b) / b)
      omega

private theorem digitSum_nonneg (b a : ℤ) : 0 ≤ negBaseSqDigitSum b a := by
  unfold negBaseSqDigitSum
  exact aux_nonneg b _ a

private theorem rem_bounds {B : ℤ} (hB : 2 ≤ B) (a : ℤ) :
    0 ≤ a % (-B) ∧ a % (-B) < B := by
  have hb : -B ≠ 0 := by omega
  refine ⟨Int.emod_nonneg _ hb, ?_⟩
  rw [Int.emod_neg]
  exact Int.emod_lt_of_pos _ (by omega)

private theorem decomp {B a : ℤ} : -B * (a / (-B)) + a % (-B) = a := by
  have h := Int.mul_ediv_add_emod a (-B)
  linarith

private theorem sq_le_sq_of_bounds {r B : ℤ} (hB : 2 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < B) :
    r ^ 2 ≤ (B - 1) ^ 2 := by
  nlinarith

private theorem digitSum_lt_of_nonneg_small {B a : ℤ} (hB : 7 ≤ B) (ha0 : 0 ≤ a)
    (ha1 : a < 5 * B ^ 2) : negBaseSqDigitSum (-B) a < 2 * B ^ 2 := by
  let r0 := a % (-B)
  let q1 := a / (-B)
  have hr0 := rem_bounds (by omega : 2 ≤ B) a
  have he0 : -B * q1 + r0 = a := decomp
  have hq1lo : -5 * B < q1 := by nlinarith
  have hq1hi : q1 ≤ 0 := by nlinarith
  let r1 := q1 % (-B)
  let q2 := q1 / (-B)
  have hr1 := rem_bounds (by omega : 2 ≤ B) q1
  have he1 : -B * q2 + r1 = q1 := decomp
  have hq2lo : 0 ≤ q2 := by nlinarith
  have hq2hi : q2 ≤ 5 := by nlinarith
  let r2 := q2 % (-B)
  let q3 := q2 / (-B)
  have hr2 := rem_bounds (by omega : 2 ≤ B) q2
  have he2 : -B * q3 + r2 = q2 := decomp
  have hq3lo : 0 ≤ q3 := by nlinarith
  have hq3hi : q3 ≤ 0 := by nlinarith
  have hq3 : q3 = 0 := by omega
  have e0 : a = -B * q1 + r0 := he0.symm
  have e1 : q1 = -B * q2 + r1 := he1.symm
  have e2 : q2 = -B * q3 + r2 := he2.symm
  have hS0 : negBaseSqDigitSum (-B) a = r0 ^ 2 + negBaseSqDigitSum (-B) q1 := by
    rw [e0]
    exact digitSum_cons (by omega) hr0.1 hr0.2
  have hS1 : negBaseSqDigitSum (-B) q1 = r1 ^ 2 + negBaseSqDigitSum (-B) q2 := by
    rw [e1]
    exact digitSum_cons (by omega) hr1.1 hr1.2
  have hS2 : negBaseSqDigitSum (-B) q2 = r2 ^ 2 + negBaseSqDigitSum (-B) q3 := by
    rw [e2]
    exact digitSum_cons (by omega) hr2.1 hr2.2
  have hSq3 : negBaseSqDigitSum (-B) q3 = 0 := by rw [hq3]; exact negBaseSqDigitSum_zero (-B)
  have hr2eq : r2 = q2 := by simpa [hq3] using he2
  have hr0sq : r0 ^ 2 ≤ (B - 1) ^ 2 := sq_le_sq_of_bounds (by omega) hr0.1 hr0.2
  have hr1sq : r1 ^ 2 ≤ (B - 1) ^ 2 := sq_le_sq_of_bounds (by omega) hr1.1 hr1.2
  have hr2sq : r2 ^ 2 ≤ 25 := by nlinarith
  rw [hS0, hS1, hS2, hSq3, add_zero]
  nlinarith

private theorem digitSum_le_of_bounded {B a : ℤ} (hB : 7 ≤ B)
    (ha0 : -5 * B ^ 2 < a) (ha1 : a < 5 * B ^ 2) :
    negBaseSqDigitSum (-B) a ≤ 4 * (B - 1) ^ 2 := by
  let r0 := a % (-B)
  let q1 := a / (-B)
  have hr0 := rem_bounds (by omega : 2 ≤ B) a
  have he0 : -B * q1 + r0 = a := decomp
  have hq1lo : -5 * B < q1 := by nlinarith
  have hq1hi : q1 ≤ 5 * B := by nlinarith
  let r1 := q1 % (-B)
  let q2 := q1 / (-B)
  have hr1 := rem_bounds (by omega : 2 ≤ B) q1
  have he1 : -B * q2 + r1 = q1 := decomp
  have hq2lo : -5 ≤ q2 := by nlinarith
  have hq2hi : q2 ≤ 5 := by nlinarith
  let r2 := q2 % (-B)
  let q3 := q2 / (-B)
  have hr2 := rem_bounds (by omega : 2 ≤ B) q2
  have he2 : -B * q3 + r2 = q2 := decomp
  have hq3lo : 0 ≤ q3 := by nlinarith
  have hq3hi : q3 ≤ 1 := by nlinarith
  let r3 := q3 % (-B)
  let q4 := q3 / (-B)
  have hr3 := rem_bounds (by omega : 2 ≤ B) q3
  have he3 : -B * q4 + r3 = q3 := decomp
  have hq4lo : 0 ≤ q4 := by nlinarith
  have hq4hi : q4 ≤ 0 := by nlinarith
  have hq4 : q4 = 0 := by omega
  have e0 : a = -B * q1 + r0 := he0.symm
  have e1 : q1 = -B * q2 + r1 := he1.symm
  have e2 : q2 = -B * q3 + r2 := he2.symm
  have e3 : q3 = -B * q4 + r3 := he3.symm
  have hS0 : negBaseSqDigitSum (-B) a = r0 ^ 2 + negBaseSqDigitSum (-B) q1 := by
    rw [e0]
    exact digitSum_cons (by omega) hr0.1 hr0.2
  have hS1 : negBaseSqDigitSum (-B) q1 = r1 ^ 2 + negBaseSqDigitSum (-B) q2 := by
    rw [e1]
    exact digitSum_cons (by omega) hr1.1 hr1.2
  have hS2 : negBaseSqDigitSum (-B) q2 = r2 ^ 2 + negBaseSqDigitSum (-B) q3 := by
    rw [e2]
    exact digitSum_cons (by omega) hr2.1 hr2.2
  have hS3 : negBaseSqDigitSum (-B) q3 = r3 ^ 2 + negBaseSqDigitSum (-B) q4 := by
    rw [e3]
    exact digitSum_cons (by omega) hr3.1 hr3.2
  have hSq4 : negBaseSqDigitSum (-B) q4 = 0 := by rw [hq4]; exact negBaseSqDigitSum_zero (-B)
  have hr0sq : r0 ^ 2 ≤ (B - 1) ^ 2 := sq_le_sq_of_bounds (by omega) hr0.1 hr0.2
  have hr1sq : r1 ^ 2 ≤ (B - 1) ^ 2 := sq_le_sq_of_bounds (by omega) hr1.1 hr1.2
  have hr2sq : r2 ^ 2 ≤ (B - 1) ^ 2 := sq_le_sq_of_bounds (by omega) hr2.1 hr2.2
  have hr3sq : r3 ^ 2 ≤ (B - 1) ^ 2 := sq_le_sq_of_bounds (by omega) hr3.1 hr3.2
  rw [hS0, hS1, hS2, hS3, hSq4, add_zero]
  nlinarith

private theorem digitSum_lt_of_large_aux {B : ℤ} (hB : 7 ≤ B) (n : ℕ) (a : ℤ)
    (hrank : digitRank a ≤ n) :
    (5 * B ^ 2 ≤ a → negBaseSqDigitSum (-B) a < a) ∧
      (a ≤ -5 * B ^ 2 → negBaseSqDigitSum (-B) a < -a) := by
  induction n generalizing a with
  | zero =>
    have ha0 : a = 0 := by
      have := Int.natAbs_eq_zero (a := a)
      unfold digitRank at hrank
      omega
    subst ha0
    have hpos : 0 < 5 * B ^ 2 := by nlinarith
    constructor <;> intro h <;> omega
  | succ n ih =>
    let r := a % (-B)
    let q := a / (-B)
    have hr := rem_bounds (by omega : 2 ≤ B) a
    have he : -B * q + r = a := decomp
    have e : a = -B * q + r := he.symm
    have hS : negBaseSqDigitSum (-B) a = r ^ 2 + negBaseSqDigitSum (-B) q := by
      rw [e]
      exact digitSum_cons (by omega) hr.1 hr.2
    have hrsq : r ^ 2 ≤ (B - 1) ^ 2 := sq_le_sq_of_bounds (by omega) hr.1 hr.2
    have hrankq : digitRank q ≤ n := by
      by_cases ha0 : a = 0
      · have he0 : -B * q + r = 0 := by simpa [ha0] using he
        have hq0lo : 0 ≤ q := by nlinarith
        have hq0hi : q ≤ 0 := by nlinarith
        have hq0 : q = 0 := by omega
        have h0 : digitRank (0 : ℤ) = 0 := by simp [digitRank]
        rw [hq0, h0]
        exact Nat.zero_le n
      · have hlt : digitRank q < digitRank a := by
          have he' : -B * q + r ≠ 0 := by rw [he]; exact ha0
          have := digitRank_lt (B := B) (q := q) (d := r) (by omega) hr.1 hr.2 he'
          rwa [he] at this
        omega
    have ihq := ih q hrankq
    constructor
    · intro ha
      have hq0 : q ≤ 0 := by nlinarith
      by_cases hqb : q ≤ -5 * B ^ 2
      · have hSq := (ihq.2 hqb)
        nlinarith
      · have hlt : -5 * B ^ 2 < q := by omega
        have hSq : negBaseSqDigitSum (-B) q ≤ 4 * (B - 1) ^ 2 := by
          apply digitSum_le_of_bounded hB
          · linarith
          · nlinarith
        nlinarith
    · intro ha
      have hq0 : 0 < q := by nlinarith
      by_cases hqb : 5 * B ^ 2 ≤ q
      · have hSq := (ihq.1 hqb)
        nlinarith
      · have hlt : q < 5 * B ^ 2 := by omega
        have hSq : negBaseSqDigitSum (-B) q ≤ 4 * (B - 1) ^ 2 := by
          apply digitSum_le_of_bounded hB
          · nlinarith
          · linarith
        nlinarith

private theorem digitSum_lt_of_large_pos {B a : ℤ} (hB : 7 ≤ B) (ha : 5 * B ^ 2 ≤ a) :
    negBaseSqDigitSum (-B) a < a :=
  (digitSum_lt_of_large_aux hB _ _ le_rfl).1 ha

private theorem iterate_one_eq (f : ℤ → ℤ) (x : ℤ) : f^[1] x = f x := by
  rw [Function.iterate_one]

private theorem exists_iterate_lt_aux {B : ℤ} (hB : 7 ≤ B) (n : ℕ) (a : ℤ) (ha0 : 0 < a)
    (hle : a.natAbs ≤ n) :
    ∃ k : ℕ, 0 < k ∧ (negBaseSqDigitSum (-B))^[k] a < 2 * B ^ 2 := by
  induction n generalizing a with
  | zero =>
    have h0 : a.natAbs = 0 := by omega
    have ha00 : a = 0 := Int.natAbs_eq_zero.mp h0
    omega
  | succ n ih =>
    by_cases ha5 : a < 5 * B ^ 2
    · refine ⟨1, one_pos, ?_⟩
      rw [iterate_one_eq]
      exact digitSum_lt_of_nonneg_small hB (by omega) ha5
    · have ha5le : 5 * B ^ 2 ≤ a := by omega
      have hSa_lt : negBaseSqDigitSum (-B) a < a :=
        digitSum_lt_of_large_pos hB ha5le
      have hSa_nonneg : 0 ≤ negBaseSqDigitSum (-B) a := digitSum_nonneg _ _
      by_cases hSa0 : negBaseSqDigitSum (-B) a = 0
      · refine ⟨1, one_pos, ?_⟩
        rw [iterate_one_eq, hSa0]
        nlinarith
      · have hSa_pos : 0 < negBaseSqDigitSum (-B) a := by omega
        have hlt : (negBaseSqDigitSum (-B) a).natAbs < a.natAbs :=
          Int.natAbs_lt_natAbs_of_nonneg_of_lt hSa_nonneg hSa_lt
        have hle' : (negBaseSqDigitSum (-B) a).natAbs ≤ n := by omega
        obtain ⟨k, hkpos, hklt⟩ := ih _ hSa_pos hle'
        refine ⟨k + 1, by omega, ?_⟩
        rw [Function.iterate_add_apply, iterate_one_eq]
        exact hklt

private theorem exists_iterate_lt_single {B a : ℤ} (hB : 7 ≤ B) (ha0 : 0 < a) :
    ∃ k : ℕ, 0 < k ∧ (negBaseSqDigitSum (-B))^[k] a < 2 * B ^ 2 :=
  exists_iterate_lt_aux hB _ _ ha0 le_rfl

private theorem iterate_stay {B x : ℤ} {m : ℕ} (hB : 7 ≤ B) (hx0 : 0 ≤ x)
    (hx1 : x < 2 * B ^ 2) : 0 ≤ (negBaseSqDigitSum (-B))^[m] x ∧
    (negBaseSqDigitSum (-B))^[m] x < 2 * B ^ 2 := by
  induction m generalizing x with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact ⟨hx0, hx1⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hprev := ih hx0 hx1
    refine ⟨digitSum_nonneg _ _, ?_⟩
    have h5 : (negBaseSqDigitSum (-B))^[m] x < 5 * B ^ 2 := by nlinarith
    exact digitSum_lt_of_nonneg_small hB hprev.1 h5

private theorem iterate_nonneg_of_pos {B x : ℤ} {k : ℕ} (hk : 0 < k) :
    0 ≤ (negBaseSqDigitSum (-B))^[k] x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [Function.iterate_succ_apply']
  exact digitSum_nonneg _ _

private theorem exists_common_iterate_lt {B : ℤ} (hB : 7 ≤ B) (A : Finset ℤ)
    (hA : ∀ a ∈ A, 0 < a) :
    ∃ K : ℕ, 0 < K ∧
      ∀ a ∈ A, (negBaseSqDigitSum (-B))^[K] a < 2 * B ^ 2 := by
  induction A using Finset.induction with
  | empty =>
    refine ⟨1, one_pos, ?_⟩
    intro a ha
    exact absurd ha (Finset.notMem_empty a)
  | insert a s _ ih =>
    have ha0 : 0 < a := by
      apply hA
      rw [Finset.mem_insert]
      exact Or.inl rfl
    have hs : ∀ t ∈ s, 0 < t := by
      intro t ht
      apply hA
      rw [Finset.mem_insert]
      exact Or.inr ht
    obtain ⟨Ka, hKa_pos, hKa_lt⟩ := exists_iterate_lt_single hB ha0
    obtain ⟨Ks, hKs_pos, hKs_all⟩ := ih hs
    let K := max Ka Ks
    have hKa_le : Ka ≤ K := Nat.le_max_left _ _
    have hKs_le : Ks ≤ K := Nat.le_max_right _ _
    have hK_pos : 0 < K := lt_of_lt_of_le hKa_pos hKa_le
    refine ⟨K, hK_pos, ?_⟩
    intro t ht
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | hts
    · have hKeq : K = (K - Ka) + Ka := (Nat.sub_add_cancel hKa_le).symm
      have hnonneg : 0 ≤ (negBaseSqDigitSum (-B))^[Ka] t :=
        iterate_nonneg_of_pos hKa_pos
      rw [hKeq, Function.iterate_add_apply]
      exact (iterate_stay hB hnonneg hKa_lt).2
    · have hlt := hKs_all t hts
      have hnonneg : 0 ≤ (negBaseSqDigitSum (-B))^[Ks] t :=
        iterate_nonneg_of_pos hKs_pos
      have hKeq : K = (K - Ks) + Ks := (Nat.sub_add_cancel hKs_le).symm
      rw [hKeq, Function.iterate_add_apply]
      exact (iterate_stay hB hnonneg hlt).2

/-- **A common iterate of the negative-base digit-square map falls below twice the squared base.**
Let $b \le -7$ be an integer, let $S_{2,b}$ be the map sending an integer to the sum of the
squares of its base-$b$ digits, and write $S_{2,b}^k$ for its $k$-fold iterate. For every finite
set $A$ of positive integers there is an integer $k \ge 1$ such that $S_{2,b}^k(a) < 2b^2$ for
every $a \in A$.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Lemma 2.2. -/
public theorem exists_iterate_negBaseSqDigitSum_lt (b : ℤ) (hb : b ≤ -7) (A : Finset ℤ)
    (hA : ∀ a ∈ A, 0 < a) :
    ∃ k : ℕ, 0 < k ∧ ∀ a ∈ A, (negBaseSqDigitSum b)^[k] a < 2 * b ^ 2 := by
  have hB : 7 ≤ -b := by omega
  obtain ⟨K, hKpos, hKall⟩ := exists_common_iterate_lt hB A hA
  have hbneg : -(-b) = b := neg_neg b
  have hb2 : (-b) ^ 2 = b ^ 2 := by ring
  refine ⟨K, hKpos, ?_⟩
  intro a ha
  have h := hKall a ha
  rw [hbneg, hb2] at h
  exact h

end MetaMathlibExt
