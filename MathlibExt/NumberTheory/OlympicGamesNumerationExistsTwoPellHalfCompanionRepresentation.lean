/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.NumberTheory.Rayleigh
public import MathlibExt.NumberTheory.BronzeMetallicIdentities
public import MathlibExt.NumberTheory.GreedyOddFibonacciFloor
public import MathlibExt.NumberTheory.OddFibonacciGoldenRatio
public import MathlibExt.NumberTheory.OddFibonacciRepresentation
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence
public import MathlibExt.NumberTheory.PellSilverRatio
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# Numeration by doubled Pell and half-companion Pell numbers

Greedy division by the mixed Pell place values produces a representation of every positive
integer. Bounds on lower partial sums imply the digit caps and excluded neighboring patterns.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 4.
-/

namespace MetaMathlibExt

open Finset

private lemma pell_pair (n : ℕ) :
    pellLucasSequence n + pellNumber n = pellNumber (n + 1) ∧
      pellLucasSequence (n + 1) = pellNumber (n + 1) + pellNumber n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    have hp : pellNumber (n + 2) = 2 * pellNumber (n + 1) + pellNumber n := rfl
    have hh := pellLucasSequence_succ_succ n
    change pellLucasSequence (n + 1) + pellNumber (n + 1) = pellNumber (n + 2) ∧
      pellLucasSequence (n + 2) = pellNumber (n + 2) + pellNumber (n + 1)
    omega

private lemma mixed_recurrence (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    (k : ℕ) :
    R (2 * k + 2) + R (2 * k) = 2 * R (2 * k + 1) ∧
      R (2 * k + 3) + R (2 * k + 1) = 4 * R (2 * k + 2) := by
  have hp := pell_pair (2 * k)
  have hp₁ := pell_pair (2 * k + 1)
  have hp₂ := pell_pair (2 * k + 2)
  have hr₁ : pellNumber (2 * k + 2) =
      2 * pellNumber (2 * k + 1) + pellNumber (2 * k) := rfl
  have hr₂ : pellNumber (2 * k + 3) =
      2 * pellNumber (2 * k + 2) + pellNumber (2 * k + 1) := rfl
  simp only [Nat.add_assoc, Nat.reduceAdd] at hp₁ hp₂
  simp [hR, Nat.add_mod]
  constructor <;> omega

private lemma mixed_growth (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    (k : ℕ) :
    0 < R (2 * k) ∧ R (2 * k) < R (2 * k + 1) ∧
      R (2 * k + 1) < R (2 * k + 2) ∧ R (2 * k + 1) < 4 * R (2 * k) := by
  induction k with
  | zero => norm_num [hR, pellNumber, pellLucasSequence]
  | succ k ih =>
    have h₁ := mixed_recurrence R hR k
    have h₂ := mixed_recurrence R hR (k + 1)
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] at *
    omega

private lemma mixed_strictMono (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k) :
    StrictMono R := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := mixed_growth R hR (n / 2)
  have hm := Nat.mod_lt n (by decide : 0 < 2)
  have hd := Nat.mod_add_div n 2
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn : n = 2 * (n / 2) := by omega
    calc
      R n = R (2 * (n / 2)) := congrArg R hn
      _ < R (2 * (n / 2) + 1) := h.2.1
      _ = R (n + 1) := congrArg R (by omega)
  · have hn : n = 2 * (n / 2) + 1 := by omega
    calc
      R n = R (2 * (n / 2) + 1) := congrArg R hn
      _ < R (2 * (n / 2) + 2) := h.2.2.1
      _ = R (n + 1) := congrArg R (by omega)

private lemma greedy_digits (R : ℕ → ℕ) (h₀ : R 0 = 1) (hmono : StrictMono R)
    (n t : ℕ) (ht : t < R n) :
    ∃ a : ℕ → ℕ, ∀ m, (∑ k ∈ range m, a k * R k) < R m ∧
      (n ≤ m → (∑ k ∈ range m, a k * R k) = t) := by
  have hpos (m : ℕ) : 0 < R m := by
    have := hmono.monotone (Nat.zero_le m)
    omega
  induction n generalizing t with
  | zero =>
    have ht₀ : t = 0 := by omega
    exact ⟨fun _ ↦ 0, fun m ↦ by simp [ht₀, hpos m]⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih (t % R n) (Nat.mod_lt _ (hpos n))
    refine ⟨fun k ↦ a k + if k = n then t / R n else 0, fun m ↦ ?_⟩
    simp only [add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq', mem_range]
    by_cases hnm : n < m
    · rw [ite_eq_left hnm, (ha m).2 hnm.le, Nat.mod_add_div']
      exact ⟨ht.trans_le (hmono.monotone hnm), fun _ ↦ rfl⟩
    · simp [hnm, (ha m).1, show ¬ n + 1 ≤ m from by omega]

private lemma prefix_single (R a : ℕ → ℕ)
    (ha : ∀ m, (∑ k ∈ range m, a k * R k) < R m) (j : ℕ) :
    a j * R j < R (j + 1) := by
  have h := ha (j + 1)
  rw [sum_range_succ] at h
  omega

private lemma prefix_pair (R a : ℕ → ℕ)
    (ha : ∀ m, (∑ k ∈ range m, a k * R k) < R m) (i j : ℕ) (hij : i < j) :
    a i * R i + a j * R j < R (j + 1) := by
  have hi : a i * R i ≤ ∑ k ∈ range j, a k * R k :=
    single_le_sum (fun k _ ↦ Nat.zero_le (a k * R k)) (mem_range.mpr hij)
  have h := ha (j + 1)
  rw [sum_range_succ] at h
  omega

private lemma mixed_previous (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    (k : ℕ) (hk : 1 ≤ k) :
    R (2 * k) + R (2 * k - 2) = 2 * R (2 * k - 1) ∧
      R (2 * k + 1) + R (2 * k - 1) = 4 * R (2 * k) := by
  have h := mixed_recurrence R hR (k - 1)
  have h₀ : 2 * (k - 1) = 2 * k - 2 := by omega
  have h₁ : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  have h₂ : 2 * (k - 1) + 2 = 2 * k := by omega
  have h₃ : 2 * (k - 1) + 3 = 2 * k + 1 := by omega
  rw [h₂, h₃, h₁, h₀] at h
  exact h

private lemma digit_conditions (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    (a : ℕ → ℕ) (ha : ∀ m, (∑ k ∈ range m, a k * R k) < R m) :
    a 0 ≤ 1 ∧ (a 1 = 1 → a 0 = 0) ∧ (∀ k, a (2 * k) ≤ 3 ∧ a (2 * k + 1) ≤ 1) ∧
      (∀ k, 1 ≤ k → a (2 * k) = 3 → a (2 * k - 1) = 0 ∧ a (2 * k + 1) = 0) ∧
      (∀ k, 1 ≤ k → a (2 * k) = 3 → a (2 * k - 2) < 3) ∧
      (∀ k, a (2 * k) = 3 → a (2 * k + 2) < 3) := by
  have h₀ : a 0 ≤ 1 := by
    have h := ha 1
    have h' : a 0 < 2 := by simpa [hR, pellNumber, pellLucasSequence] using h
    exact Nat.le_of_lt_succ h'
  have hlow : a 1 = 1 → a 0 = 0 := by
    intro h₁
    have h := ha 2
    simp [sum_range_succ, hR, pellNumber, pellLucasSequence, h₁] at h
    omega
  have hbound (k : ℕ) : a (2 * k) ≤ 3 ∧ a (2 * k + 1) ≤ 1 := by
    have hg := mixed_growth R hR k
    have hr := mixed_recurrence R hR k
    constructor
    · have h := prefix_single R a ha (2 * k)
      by_contra! hb
      have := Nat.mul_le_mul_right (R (2 * k)) hb
      omega
    · have h := prefix_single R a ha (2 * k + 1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at h
      by_contra! hb
      have := Nat.mul_le_mul_right (R (2 * k + 1)) hb
      omega
  have hnext (k : ℕ) (hk : a (2 * k) = 3) : a (2 * k + 1) = 0 := by
    have hg := mixed_growth R hR k
    have hr := mixed_recurrence R hR k
    have h := prefix_pair R a ha (2 * k) (2 * k + 1) (by omega)
    simp only [hk, Nat.add_assoc, Nat.reduceAdd] at h
    by_contra! hn
    have := Nat.mul_le_mul_right (R (2 * k + 1)) (show 1 ≤ a (2 * k + 1) by omega)
    omega
  have hpair (k : ℕ) (hk : a (2 * k) = 3) : a (2 * k + 2) < 3 := by
    have hg := mixed_growth R hR k
    have hr := mixed_recurrence R hR k
    have h := prefix_pair R a ha (2 * k) (2 * k + 2) (by omega)
    simp only [hk, Nat.add_assoc, Nat.reduceAdd] at h
    by_contra! hn
    have := Nat.mul_le_mul_right (R (2 * k + 2)) hn
    omega
  refine ⟨h₀, hlow, hbound, ?_, ?_, hpair⟩
  · intro k hk hd
    refine ⟨?_, hnext k hd⟩
    have hr := mixed_previous R hR k hk
    have h := prefix_pair R a ha (2 * k - 1) (2 * k) (by omega)
    rw [hd] at h
    by_contra! hn
    have := Nat.mul_le_mul_right (R (2 * k - 1)) (show 1 ≤ a (2 * k - 1) by omega)
    omega
  · intro k hk hd
    have h := hpair (k - 1)
    have h₁ : 2 * (k - 1) = 2 * k - 2 := by omega
    have h₂ : 2 * (k - 1) + 2 = 2 * k := by omega
    rw [h₂, h₁] at h
    have hb := (hbound (k - 1)).1
    rw [h₁] at hb
    by_contra! hn
    have he : a (2 * k - 2) = 3 := by omega
    have := h he
    omega

private lemma exists_place (R : ℕ → ℕ) (h₀ : R 0 = 1) (hmono : StrictMono R)
    (t : ℕ) (ht : 0 < t) : ∃ n, R n ≤ t ∧ t < R (n + 1) := by
  have hex : ∃ m, t < R m := by
    refine ⟨t + 1, ?_⟩
    have h := hmono.add_le_nat (t + 1) 0
    simp only [h₀, Nat.add_zero] at h
    omega
  let m := Nat.find hex
  have hm : t < R m := Nat.find_spec hex
  have hm₀ : 0 < m := by
    by_contra! h
    have he : m = 0 := by omega
    rw [he, h₀] at hm
    omega
  refine ⟨m - 1, ?_, ?_⟩
  · have h := Nat.find_min hex (show m - 1 < m by omega)
    omega
  · have he : m - 1 + 1 = m := by omega
    simpa only [he] using hm

@[expose] public section

/-- **Numeration by doubled Pell and half-companion Pell numbers.** Let $P_n$ be the Pell numbers
($P_0 = 0$, $P_1 = 1$, $P_{n+2} = 2P_{n+1} + P_n$) and $H_n$ the half-companion Pell numbers
($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$), and let $R_k = 2P_k$ for odd $k$ and
$R_k = H_k$ for even $k$. Then for every positive integer $t$ there are a natural number $n$ and
natural numbers $a_0, a_1, a_2, \dots$ such that $R_n \le t < R_{n+1}$,
$t = \sum_{k=0}^{n} a_k R_k$, $a_0 \le 1$, $a_0 = 0$ if $a_1 = 1$, $a_{2k} \le 3$ and
$a_{2k+1} \le 1$ for every $k \ge 0$, $a_{2k+2} < 3$ whenever $a_{2k} = 3$ ($k \ge 0$), and
$a_{2k-1} = a_{2k+1} = 0$ and $a_{2k-2} < 3$ whenever $a_{2k} = 3$ with $k \ge 1$.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 4. -/
public theorem exists_two_pell_halfCompanion_representation (R : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then 2 * pellNumber k else pellLucasSequence k)
    {t : ℕ} (ht : 0 < t) :
    ∃ (n : ℕ) (a : ℕ → ℕ), R n ≤ t ∧ t < R (n + 1) ∧
      t = ∑ k ∈ range (n + 1), a k * R k ∧
      a 0 ≤ 1 ∧ (a 1 = 1 → a 0 = 0) ∧ (∀ k, a (2 * k) ≤ 3 ∧ a (2 * k + 1) ≤ 1) ∧
      (∀ k, 1 ≤ k → a (2 * k) = 3 → a (2 * k - 1) = 0 ∧ a (2 * k + 1) = 0) ∧
      (∀ k, 1 ≤ k → a (2 * k) = 3 → a (2 * k - 2) < 3) ∧
      (∀ k, a (2 * k) = 3 → a (2 * k + 2) < 3) := by
  have h₀ : R 0 = 1 := by simp [hR]
  have hmono := mixed_strictMono R hR
  obtain ⟨n, hlo, hhi⟩ := exists_place R h₀ hmono t ht
  obtain ⟨a, ha⟩ := greedy_digits R h₀ hmono (n + 1) t hhi
  exact ⟨n, a, hlo, hhi, ((ha (n + 1)).2 le_rfl).symm,
    digit_conditions R hR a (fun m ↦ (ha m).1)⟩

end

end MetaMathlibExt
