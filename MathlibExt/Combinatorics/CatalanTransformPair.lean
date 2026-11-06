/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

section
namespace MetaMathlibExt

private lemma ballot_aux (n k : ℕ) (hk : k ≤ n) :
    ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) *
      (Nat.choose (2 * n) (n - k) : ℚ)
    = (Nat.choose (2 * n) (n - k) : ℚ) - (Nat.choose (2 * n) (n + k + 1) : ℚ) := by
  have hn1 : ((n : ℚ) + (k : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  rcases eq_or_lt_of_le hk with h_eq | hlt
  · subst h_eq
    simp only [Nat.choose_eq_zero_of_lt (show 2 * k < k + k + 1 by omega), Nat.cast_zero,
      sub_zero]
    ring
  · have hnk : n - k - 1 + 1 = n - k := by omega
    have hnk2 : 2 * n - (n - k - 1) = n + k + 1 := by omega
    have hkey := Nat.choose_succ_right_eq (2 * n) (n - k - 1)
    rw [hnk] at hkey
    rw [hnk2] at hkey
    have hle : n + k + 1 ≤ 2 * n := by omega
    have hsymm : Nat.choose (2 * n) (n - k - 1) = Nat.choose (2 * n) (n + k + 1) := by
      have h := Nat.choose_symm hle
      have hsub : 2 * n - (n + k + 1) = n - k - 1 := by omega
      rw [hsub] at h
      exact h
    have hkeyQ : ((Nat.choose (2 * n) (n - k) : ℚ)) * ((n : ℚ) - (k : ℚ))
        = ((Nat.choose (2 * n) (n + k + 1) : ℚ)) * ((n : ℚ) + (k : ℚ) + 1) := by
      exact_mod_cast hkey.trans (by rw [hsymm])
    linear_combination -hkeyQ

private lemma alt_vandermonde (j N m : ℕ) :
    (∑ r ∈ Finset.range (m + 1), (-1 : ℚ) ^ r * (Nat.choose (j + r) j : ℚ) *
      (Nat.choose N (m - r) : ℚ))
    = Ring.choose ((N : ℚ) - (j : ℚ) - 1) m := by
  have hterm : ∀ r : ℕ, (-1 : ℚ) ^ r * (Nat.choose (j + r) j : ℚ) *
      (Nat.choose N (m - r) : ℚ)
      = Ring.choose (-((j : ℚ) + 1)) r * Ring.choose (N : ℚ) (m - r) := by
    intro r
    have hneg := Ring.choose_neg (R := ℚ) ((j : ℚ) + 1) r
    rw [Units.smul_def, zsmul_eq_mul, Int.coe_negOnePow_natCast] at hneg
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one] at hneg
    have hsub : ((j : ℚ) + 1 + (r : ℚ) - 1) = ((j + r : ℕ) : ℚ) := by push_cast; ring
    rw [hsub, Ring.choose_natCast] at hneg
    have hsub2 : j + r - r = j := by omega
    have hbase := Nat.choose_symm (show r ≤ j + r by omega)
    rw [hsub2] at hbase
    rw [hbase.symm] at hneg
    have hN : Ring.choose (N : ℚ) (m - r) = ((Nat.choose N (m - r) : ℚ)) := by
      rw [Ring.choose_natCast]
    rw [hN, hneg]
  simp_rw [hterm]
  have hvand := Ring.add_choose_eq (R := ℚ) (r := -((j : ℚ) + 1)) (s := (N : ℚ)) m
    (Commute.all _ _)
  have hadd : -((j : ℚ) + 1) + (N : ℚ) = (N : ℚ) - (j : ℚ) - 1 := by ring
  rw [hadd] at hvand
  rw [hvand, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private lemma S1_eval (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k - j) *
      (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ))
    = ((Nat.choose (2 * n - j - 1) (n - j) : ℕ) : ℚ) := by
  have hsub1 : n + 1 - j = n - j + 1 := by omega
  have hstep : (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k - j) *
      (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ))
      = ∑ r ∈ Finset.range (n - j + 1), (-1 : ℚ) ^ r *
        (Nat.choose (j + r) j : ℚ) * (Nat.choose (2 * n) (n - j - r) : ℚ) := by
    have hvan : ∀ k ∈ Finset.range (n + 1), k ∉ Finset.Ico j (n + 1) →
        (-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n - k) : ℚ) *
          (Nat.choose k j : ℚ) = 0 := by
      intro k hk hnk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico] at hnk
      have hkj : k < j := by omega
      have h0 : Nat.choose k j = 0 := Nat.choose_eq_zero_of_lt hkj
      simp [h0]
    have hsub : Finset.Ico j (n + 1) ⊆ Finset.range (n + 1) := by
      intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      omega
    have hrestr : (∑ k ∈ Finset.Ico j (n + 1), (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ))
        = ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k - j) *
          (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) :=
      Finset.sum_subset hsub hvan
    rw [← hrestr]
    have hre := Finset.sum_Ico_eq_sum_range (fun k => (-1 : ℚ) ^ (k - j) *
      (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ)) j (n + 1)
    rw [hsub1] at hre
    rw [hre]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_range] at hr
    have hr1 : j + r - j = r := by omega
    have hr2 : n - (j + r) = n - j - r := by omega
    rw [hr1, hr2]
    ring
  rw [hstep]
  have hv := alt_vandermonde j (2 * n) (n - j)
  rw [hv]
  have hcast : ((2 * n : ℕ) : ℚ) - (j : ℚ) - 1 = (((2 * n - j - 1 : ℕ)) : ℚ) := by
    have h1 : j ≤ 2 * n := by omega
    have h2 : 1 ≤ 2 * n - j := by omega
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
    push_cast
    ring
  rw [hcast, Ring.choose_natCast]

-- S2, diagonal case: sum is 0 when j = n
private lemma S2_eq (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k - n) *
      (Nat.choose (2 * n) (n + k + 1) : ℚ) * (Nat.choose k n : ℚ)) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_range] at hk
  have hkn : k ≤ n := by omega
  rcases eq_or_lt_of_le hkn with h_eq | hlt
  · rw [h_eq]
    have h0 : Nat.choose (2 * n) (n + n + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]
  · have h0 : Nat.choose k n = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]

-- S2, off-diagonal: equals C(2n-j-1, n-j-1) for j < n
private lemma S2_lt (n j : ℕ) (hn : 0 < n) (hj : j < n) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k - j) *
      (Nat.choose (2 * n) (n + k + 1) : ℚ) * (Nat.choose k j : ℚ))
    = ((Nat.choose (2 * n - j - 1) (n - j - 1) : ℕ) : ℚ) := by
  -- step 1: k = n term vanishes; restrict to range n
  have htop : (-1 : ℚ) ^ (n - j) * (Nat.choose (2 * n) (n + n + 1) : ℚ) *
      (Nat.choose n j : ℚ) = 0 := by
    have h0 : Nat.choose (2 * n) (n + n + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [h0]
  have hrestr : (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k - j) *
      (Nat.choose (2 * n) (n + k + 1) : ℚ) * (Nat.choose k j : ℚ))
      = ∑ k ∈ Finset.range n, (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n + k + 1) : ℚ) * (Nat.choose k j : ℚ) := by
    rw [Finset.sum_range_succ, htop, add_zero]
  rw [hrestr]
  -- step 2: symmetry C(2n, n+k+1) = C(2n, n-k-1) for k < n
  have hsymm : ∀ k ∈ Finset.range n,
      (Nat.choose (2 * n) (n + k + 1) : ℚ)
      = ((Nat.choose (2 * n) (n - k - 1) : ℕ) : ℚ) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hle : n + k + 1 ≤ 2 * n := by omega
    have h := Nat.choose_symm hle
    have hsub : 2 * n - (n + k + 1) = n - k - 1 := by omega
    rw [hsub] at h
    exact_mod_cast h.symm
  have hstep0 : (∑ k ∈ Finset.range n, (-1 : ℚ) ^ (k - j) *
      (Nat.choose (2 * n) (n + k + 1) : ℚ) * (Nat.choose k j : ℚ))
      = ∑ k ∈ Finset.range n, (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k - 1) : ℚ) * (Nat.choose k j : ℚ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsymm k hk]
  rw [hstep0]
  -- step 3: reindex k = j + r, r in range (n - j)
  have hsub1 : n - j = (n - j - 1) + 1 := by omega
  have hstep : (∑ k ∈ Finset.range n, (-1 : ℚ) ^ (k - j) *
      (Nat.choose (2 * n) (n - k - 1) : ℚ) * (Nat.choose k j : ℚ))
      = ∑ r ∈ Finset.range (n - j), (-1 : ℚ) ^ r *
        (Nat.choose (j + r) j : ℚ) * (Nat.choose (2 * n) (n - j - 1 - r) : ℚ) := by
    have hvan : ∀ k ∈ Finset.range n, k ∉ Finset.Ico j n →
        (-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n - k - 1) : ℚ) *
          (Nat.choose k j : ℚ) = 0 := by
      intro k hk hnk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico] at hnk
      have hkj : k < j := by omega
      have h0 : Nat.choose k j = 0 := Nat.choose_eq_zero_of_lt hkj
      simp [h0]
    have hsub : Finset.Ico j n ⊆ Finset.range n := by
      intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      omega
    have hrestr2 : (∑ k ∈ Finset.Ico j n, (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k - 1) : ℚ) * (Nat.choose k j : ℚ))
        = ∑ k ∈ Finset.range n, (-1 : ℚ) ^ (k - j) *
          (Nat.choose (2 * n) (n - k - 1) : ℚ) * (Nat.choose k j : ℚ) :=
      Finset.sum_subset hsub hvan
    rw [← hrestr2]
    have hre := Finset.sum_Ico_eq_sum_range (fun k => (-1 : ℚ) ^ (k - j) *
      (Nat.choose (2 * n) (n - k - 1) : ℚ) * (Nat.choose k j : ℚ)) j n
    rw [hre]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.mem_range] at hr
    have hr1 : j + r - j = r := by omega
    have hr2 : n - (j + r) - 1 = n - j - 1 - r := by omega
    rw [hr1, hr2]
    ring
  rw [hstep]
  have hv := alt_vandermonde j (2 * n) (n - j - 1)
  rw [← hsub1] at hv
  rw [hv]
  have hcast : ((2 * n : ℕ) : ℚ) - (j : ℚ) - 1 = (((2 * n - j - 1 : ℕ)) : ℚ) := by
    have h1 : j ≤ 2 * n := by omega
    have h2 : 1 ≤ 2 * n - j := by omega
    rw [Nat.cast_sub h2, Nat.cast_sub h1]
    push_cast
    ring
  rw [hcast, Ring.choose_natCast]

private lemma recomb_lt (n j : ℕ) (hn : 0 < n) (hj : j < n) :
    ((Nat.choose (2 * n - j - 1) (n - j) : ℕ) : ℚ)
      - ((Nat.choose (2 * n - j - 1) (n - j - 1) : ℕ) : ℚ)
    = (j : ℚ) / (((2 * n : ℕ) : ℚ) - (j : ℚ)) * ((Nat.choose (2 * n - j) (n - j) : ℕ) : ℚ) := by
  set M := 2 * n - j - 1 with hM
  set N := 2 * n - j with hN
  set K := n - j with hK
  set L := n - j - 1 with hL
  have hMN : M + 1 = N := by omega
  have hMK : M + 1 - K = n := by omega
  have hLK : L + 1 = K := by omega
  have hML : M - L = n := by omega
  have hKN : K + j = n := by omega
  have hN1 : 1 ≤ N := by omega
  have hK1 : 1 ≤ K := by omega
  have hNK : N - K = n := by omega
  have key1nat := Nat.choose_mul_succ_eq M K
  rw [hMN, hNK] at key1nat
  -- key1nat : C(M,K) * N = C(N,K) * n
  have key2nat := Nat.choose_succ_right_eq M L
  rw [hLK, hML] at key2nat
  -- key2nat : C(M,K) * K = C(M,L) * n
  have key1 : ((Nat.choose M K : ℕ) : ℚ) * (N : ℚ) = ((Nat.choose N K : ℕ) : ℚ) * (n : ℚ) := by
    exact_mod_cast key1nat
  have key2 : ((Nat.choose M K : ℕ) : ℚ) * (K : ℚ) = ((Nat.choose M L : ℕ) : ℚ) * (n : ℚ) := by
    exact_mod_cast key2nat
  have hN' : (N : ℚ) ≠ 0 := by
    have : 0 < N := by omega
    exact_mod_cast (by omega : N ≠ 0)
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hcastN : ((N : ℕ) : ℚ) = ((2 * n : ℕ) : ℚ) - (j : ℚ) := by
    rw [hN]
    have h1 : j ≤ 2 * n := by omega
    rw [Nat.cast_sub h1]
  have hcastK : ((K : ℕ) : ℚ) = (n : ℚ) - (j : ℚ) := by
    rw [hK, Nat.cast_sub (by omega : j ≤ n)]
  have e1 : ((Nat.choose M K : ℕ) : ℚ) = ((Nat.choose N K : ℕ) : ℚ) * (n : ℚ) / (N : ℚ) := by
    rw [eq_div_iff hN']
    exact key1
  have e2 : ((Nat.choose M L : ℕ) : ℚ) = ((Nat.choose M K : ℕ) : ℚ) * (K : ℚ) / (n : ℚ) := by
    rw [eq_div_iff hn']
    exact key2.symm
  have hdiv : ((2 * n : ℕ) : ℚ) - (j : ℚ) ≠ 0 := by
    rw [← hcastN]
    exact hN'
  rw [e2, e1, hcastN, hcastK]
  field_simp
  ring

-- Coefficient sum: inner sum over k collapses to the single-sum coefficient
private lemma coeff_sum (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) :
    (∑ k ∈ Finset.range (n + 1), ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) *
      (-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ))
    = ((j : ℚ) / (2 * (n : ℚ) - (j : ℚ))) * ((Nat.choose (2 * n - j) (n - j) : ℕ) : ℚ) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) *
        (-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ)
      = ((-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ))
        - ((-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n + k + 1) : ℚ) * (Nat.choose k j : ℚ)) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hb := ballot_aux n k (by omega)
    linear_combination ((-1 : ℚ) ^ (k - j)) * ((Nat.choose k j : ℕ) : ℚ) * hb
  have hsplit : (∑ k ∈ Finset.range (n + 1), ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) *
      (-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ))
      = (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k - j) *
          (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ))
        - (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (k - j) *
          (Nat.choose (2 * n) (n + k + 1) : ℚ) * (Nat.choose k j : ℚ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k hk => hterm k hk)
  rcases eq_or_lt_of_le hj with hjn | hjlt
  · rw [hjn] at hsplit ⊢
    have hS1 := S1_eval n n hn le_rfl
    have hS2 := S2_eq n
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have e1 : 2 * n - n - 1 = n - 1 := by omega
    have e2 : n - n = 0 := by omega
    have e3 : 2 * n - n = n := by omega
    have e4 : 2 * (n : ℚ) - (n : ℚ) = (n : ℚ) := by ring
    rw [hsplit, hS1, hS2, sub_zero, e1, e2, e3]
    rw [Nat.choose_zero_right, Nat.choose_zero_right, Nat.cast_one, mul_one, e4,
      div_self hn']
  · have hS1 := S1_eval n j hn (by omega)
    have hS2 := S2_lt n j hn hjlt
    have hr := recomb_lt n j hn hjlt
    have h2 : ((2 * n : ℕ) : ℚ) = 2 * (n : ℚ) := by push_cast; ring
    rw [h2] at hr
    rw [hsplit, hS1, hS2]
    exact hr

-- First single-sum form as a standalone lemma
private lemma first_form (a b : ℕ → ℚ)
    (h : ∀ n, b n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) * (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) * a j)
    (n : ℕ) (hn : 0 < n) :
    b n = ∑ k ∈ Finset.range (n + 1),
      ((k : ℚ) / (2 * (n : ℚ) - (k : ℚ))) * (Nat.choose (2 * n - k) (n - k) : ℚ) * a k := by
  rw [h n]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hfac : (∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) * (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) * a j)
      = (∑ k ∈ Finset.range (n + 1), ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) *
        (-1 : ℚ) ^ (k - j) * (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ)) * a j := by
    rw [Finset.sum_mul]
  rw [hfac, coeff_sum n j hn (by omega)]

-- Termwise equality between the two single-sum coefficients
private lemma second_termwise (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    ((k : ℚ) / (2 * (n : ℚ) - (k : ℚ))) * ((Nat.choose (2 * n - k) (n - k) : ℕ) : ℚ)
    = ((k : ℚ) / (n : ℚ)) * ((Nat.choose (2 * n - k - 1) (n - k) : ℕ) : ℚ) := by
  have hMN : 2 * n - k - 1 + 1 = 2 * n - k := by omega
  have hNK : 2 * n - k - (n - k) = n := by omega
  have keynat := Nat.choose_mul_succ_eq (2 * n - k - 1) (n - k)
  rw [hMN, hNK] at keynat
  have key : ((Nat.choose (2 * n - k - 1) (n - k) : ℕ) : ℚ) * ((2 * n - k : ℕ) : ℚ)
      = ((Nat.choose (2 * n - k) (n - k) : ℕ) : ℚ) * (n : ℚ) := by
    exact_mod_cast keynat
  have hcastN : ((2 * n - k : ℕ) : ℚ) = 2 * (n : ℚ) - (k : ℚ) := by
    rw [Nat.cast_sub (by omega : k ≤ 2 * n), Nat.cast_mul, Nat.cast_ofNat]
  have hN' : ((2 * n - k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n - k ≠ 0)
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [← hcastN]
  field_simp
  linear_combination -(k : ℚ) * key

-- Second single-sum form follows termwise from the first
private lemma second_form (a b : ℕ → ℚ)
    (h : ∀ n, b n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) * (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) * a j)
    (n : ℕ) (hn : 0 < n) :
    b n = ∑ k ∈ Finset.range (n + 1),
      ((k : ℚ) / (n : ℚ)) * (Nat.choose (2 * n - k - 1) (n - k) : ℚ) * a k := by
  have h1 := first_form a b h n hn
  rw [h1]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [second_termwise n k hn (by omega)]

private noncomputable def CatQ : PowerSeries ℚ :=
  PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries

private lemma CatQ_const : PowerSeries.constantCoeff CatQ = 1 := by
  have hcc : PowerSeries.constantCoeff PowerSeries.catalanSeries = 1 := by
    rw [PowerSeries.catalanSeries, PowerSeries.constantCoeff_mk, catalan_zero]
  rw [CatQ, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, hcc, map_one]

private lemma CatQ_eq : CatQ ^ 2 * PowerSeries.X + 1 = CatQ := by
  unfold CatQ
  have h := PowerSeries.catalanSeries_sq_mul_X_add_one
  apply_fun PowerSeries.map (Nat.castRingHom ℚ) at h
  simpa using h

private lemma CatQ_succ (j : ℕ) : CatQ ^ (j + 1) = CatQ ^ j + PowerSeries.X * CatQ ^ (j + 2) := by
  linear_combination -(CatQ ^ j) * CatQ_eq

private lemma fuss_step (j q : ℕ) :
    (((j + 1 : ℕ)) : ℚ) / (((j + 1 + 2 * (q + 1) : ℕ)) : ℚ) *
      ((Nat.choose (j + 1 + 2 * (q + 1)) (q + 1) : ℕ) : ℚ)
    = (((j : ℕ)) : ℚ) / (((j + 2 * (q + 1) : ℕ)) : ℚ) *
        ((Nat.choose (j + 2 * (q + 1)) (q + 1) : ℕ) : ℚ)
      + (((j + 2 : ℕ)) : ℚ) / (((j + 2 + 2 * q : ℕ)) : ℚ) *
        ((Nat.choose (j + 2 + 2 * q) q : ℕ) : ℚ) := by
  set N := j + 2 * (q + 1) with hNdef
  have hN1 : j + 1 + 2 * (q + 1) = N + 1 := by omega
  have hN2 : j + 2 + 2 * q = N := by omega
  rw [hN1, hN2]
  have hj1 : ((j + 1 : ℕ) : ℚ) = (j : ℚ) + 1 := by push_cast; ring
  have hj2 : ((j + 2 : ℕ) : ℚ) = (j : ℚ) + 2 := by push_cast; ring
  have hq1 : ((q + 1 : ℕ) : ℚ) = (q : ℚ) + 1 := by push_cast; ring
  have hNp1 : ((N + 1 : ℕ) : ℚ) = (N : ℚ) + 1 := by push_cast; ring
  rw [hj1, hj2, hNp1]
  have hNcast : (N : ℚ) = (j : ℚ) + 2 * ((q : ℚ) + 1) := by
    rw [hNdef]; push_cast; ring
  have hN' : (N : ℚ) ≠ 0 := by
    have : 1 ≤ N := by omega
    exact_mod_cast (by omega : N ≠ 0)
  have hNp1' : (N : ℚ) + 1 ≠ 0 := by
    have : (0 : ℚ) ≤ (N : ℚ) := by positivity
    linarith
  have hNq : (N : ℚ) - (q : ℚ) ≠ 0 := by
    have h1 : (N : ℚ) - (q : ℚ) = ((N - q : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : q ≤ N)]
    have h2 : N - q ≠ 0 := by omega
    rw [h1]
    exact_mod_cast h2
  have hsub : N + 1 - (q + 1) = N - q := by omega
  have key1nat := Nat.choose_mul_succ_eq N (q + 1)
  rw [hsub] at key1nat
  have key2nat := Nat.choose_succ_right_eq N q
  have hNqcast : ((N - q : ℕ) : ℚ) = (N : ℚ) - (q : ℚ) := by
    rw [Nat.cast_sub (by omega : q ≤ N)]
  have key1 : ((Nat.choose N (q + 1) : ℕ) : ℚ) * ((N : ℚ) + 1)
      = ((Nat.choose (N + 1) (q + 1) : ℕ) : ℚ) * ((N : ℚ) - (q : ℚ)) := by
    have h := congrArg (Nat.cast (R := ℚ)) key1nat
    simp only [Nat.cast_mul] at h
    rw [hNp1, hNqcast] at h
    exact h
  have key2 : ((Nat.choose N (q + 1) : ℕ) : ℚ) * ((q : ℚ) + 1)
      = ((Nat.choose N q : ℕ) : ℚ) * ((N : ℚ) - (q : ℚ)) := by
    have h := congrArg (Nat.cast (R := ℚ)) key2nat
    simp only [Nat.cast_mul] at h
    rw [hq1, hNqcast] at h
    exact h
  have eCc : ((Nat.choose N q : ℕ) : ℚ) * ((N : ℚ) + 1)
      = ((Nat.choose (N + 1) (q + 1) : ℕ) : ℚ) * ((q : ℚ) + 1) := by
    have h0 : ((N : ℚ) - (q : ℚ)) *
        (((Nat.choose N q : ℕ) : ℚ) * ((N : ℚ) + 1)
          - ((Nat.choose (N + 1) (q + 1) : ℕ) : ℚ) * ((q : ℚ) + 1)) = 0 := by
      linear_combination ((q : ℚ) + 1) * key1 - ((N : ℚ) + 1) * key2
    have hze := (mul_eq_zero.mp h0).resolve_left hNq
    linarith
  field_simp
  linear_combination (-(j : ℚ)) * key1 + (-((j : ℚ) + 2)) * eCc
    + ((Nat.choose (N + 1) (q + 1) : ℕ) : ℚ) * hNcast

-- Coefficient of x^p in CatQ^j (Fuss-Catalan formula)
private lemma Cpow_coeff : ∀ (p j : ℕ), 0 < j →
    PowerSeries.coeff p (CatQ ^ j)
    = ((j : ℚ) / ((j + 2 * p : ℕ) : ℚ)) * ((Nat.choose (j + 2 * p) p : ℕ) : ℚ) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro j hj
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · have h1 : PowerSeries.coeff 0 (CatQ ^ j) = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, CatQ_const, one_pow]
      have hj' : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have e1 : j + 2 * 0 = j := by omega
      rw [h1, e1, Nat.choose_zero_right, Nat.cast_one]
      rw [div_self hj', mul_one]
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have hj1 : 1 ≤ j := hj
      induction j, hj1 using Nat.le_induction with
      | base =>
        rw [pow_one]
        have hC : CatQ = 1 + PowerSeries.X * CatQ ^ 2 := by
          linear_combination -CatQ_eq
        rw [hC, map_add, PowerSeries.coeff_one,
          ite_eq_right (show q + 1 ≠ 0 by omega), zero_add,
          PowerSeries.coeff_succ_X_mul]
        have h2 := ih q (by omega) 2 (by omega)
        rw [h2]
        have hF := fuss_step 0 q
        simp only [zero_add] at hF
        have hmid : (((0 : ℕ)) : ℚ) / (((2 * (q + 1) : ℕ)) : ℚ) *
            ((Nat.choose (2 * (q + 1)) (q + 1) : ℕ) : ℚ) = 0 := by
          rw [Nat.cast_zero, zero_div, zero_mul]
        rw [hF, hmid, zero_add]
      | succ j hj1 ihj =>
        have hCj := CatQ_succ j
        rw [hCj, map_add, PowerSeries.coeff_succ_X_mul]
        have e2 := ih q (by omega) (j + 2) (by omega)
        have e1 := ihj (by omega)
        rw [e1, e2]
        exact (fuss_step j q).symm

private noncomputable def CatF : PowerSeries ℚ := PowerSeries.X * CatQ
private noncomputable def CatG : PowerSeries ℚ := PowerSeries.X - PowerSeries.X ^ 2

private lemma CatF_subst : PowerSeries.HasSubst CatF :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    change PowerSeries.constantCoeff (PowerSeries.X * CatQ) = 0
    rw [map_mul, PowerSeries.constantCoeff_X, zero_mul])

private lemma CatG_subst : PowerSeries.HasSubst CatG :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    change PowerSeries.constantCoeff (PowerSeries.X - PowerSeries.X ^ 2) = 0
    rw [map_sub, map_pow, PowerSeries.constantCoeff_X]
    simp)

private lemma CatG_coeff_one : PowerSeries.coeff 1 CatG = 1 := by
  have hXX : CatG = PowerSeries.X * (1 - PowerSeries.X) := by unfold CatG; ring
  have h1 : PowerSeries.coeff 1 CatG = PowerSeries.coeff 0 (1 - PowerSeries.X) := by
    rw [hXX]
    exact PowerSeries.coeff_succ_X_mul 0 (1 - PowerSeries.X)
  rw [h1, PowerSeries.coeff_zero_eq_constantCoeff, map_sub,
    PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X, sub_zero]

-- Substituting F into G gives X (since F - F^2 = X via the Catalan equation)
private lemma subst_F_G : PowerSeries.subst CatF CatG = PowerSeries.X := by
  unfold CatG
  rw [PowerSeries.subst_sub CatF_subst, PowerSeries.subst_X CatF_subst,
    PowerSeries.subst_pow CatF_subst, PowerSeries.subst_X CatF_subst]
  change CatF - CatF ^ 2 = PowerSeries.X
  have eF : CatF = PowerSeries.X * CatQ := by rw [CatF]
  rw [eF]
  linear_combination -(PowerSeries.X) * CatQ_eq

-- The other composition, via the compositional-inverse criterion
private lemma subst_G_F : PowerSeries.subst CatG CatF = PowerSeries.X :=
  PowerSeries.subst_eq_X_of_subst_eq_X CatG
    (by
      change PowerSeries.constantCoeff (PowerSeries.X - PowerSeries.X ^ 2) = 0
      rw [map_sub, map_pow, PowerSeries.constantCoeff_X]
      simp)
    (by rw [CatG_coeff_one]; exact isUnit_one)
    CatF_subst subst_F_G

private lemma one_sub_X_pow (d : ℕ) : ((1 - PowerSeries.X) ^ d : PowerSeries ℚ)
    = ∑ m ∈ Finset.range (d + 1),
      (((Nat.choose d m : ℕ) : ℚ) * (-1 : ℚ) ^ m) • PowerSeries.X ^ m := by
  have hadd := add_pow (1 : PowerSeries ℚ) (-PowerSeries.X) d
  have h1 : ((1 - PowerSeries.X) : PowerSeries ℚ) = 1 + -PowerSeries.X := by ring
  rw [h1, hadd]
  have e1 : (∑ m ∈ Finset.range (d + 1),
        (1 : PowerSeries ℚ) ^ m * (-PowerSeries.X) ^ (d - m) *
          ((Nat.choose d m : ℕ) : PowerSeries ℚ))
      = ∑ m ∈ Finset.range (d + 1),
        (1 : PowerSeries ℚ) ^ (d + 1 - 1 - m) * (-PowerSeries.X) ^ (d - (d + 1 - 1 - m)) *
          ((Nat.choose d (d + 1 - 1 - m) : ℕ) : PowerSeries ℚ) :=
    (Finset.sum_range_reflect _ _).symm
  rw [e1]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  have e : d + 1 - 1 - m = d - m := by omega
  have e2 : d - (d - m) = m := by omega
  have hC : Nat.choose d (d - m) = Nat.choose d m := Nat.choose_symm (by omega)
  have hCm1 : ((-1 : PowerSeries ℚ)) = PowerSeries.C (-1 : ℚ) := by
    rw [map_neg, map_one]
  have hneg : (-PowerSeries.X : PowerSeries ℚ) ^ m
      = PowerSeries.C ((-1 : ℚ) ^ m) * PowerSeries.X ^ m := by
    rw [neg_eq_neg_one_mul, mul_pow, hCm1, map_pow]
  rw [e, e2, hC, one_pow, one_mul, hneg,
    (map_natCast PowerSeries.C (Nat.choose d m)).symm,
    PowerSeries.smul_eq_C_mul, map_mul]
  ring

private lemma Gpow_coeff (d n : ℕ) (hdn : d ≤ n) :
    PowerSeries.coeff n (CatG ^ d)
    = ((Nat.choose d (n - d) : ℕ) : ℚ) * (-1 : ℚ) ^ (n - d) := by
  have hG : CatG = PowerSeries.X * (1 - PowerSeries.X) := by unfold CatG; ring
  have hGd : CatG ^ d = PowerSeries.X ^ d * (1 - PowerSeries.X) ^ d := by
    rw [hG, mul_pow]
  have hcc : PowerSeries.coeff n (CatG ^ d)
      = PowerSeries.coeff (n - d) ((1 - PowerSeries.X) ^ d) := by
    rw [hGd]
    have e : n = (n - d) + d := by omega
    nth_rewrite 1 [e]
    exact PowerSeries.coeff_X_pow_mul _ _ _
  have hterm : ∀ m ∈ Finset.range (d + 1),
      PowerSeries.coeff (n - d) ((((Nat.choose d m : ℕ) : ℚ) * (-1 : ℚ) ^ m) • PowerSeries.X ^ m)
      = (if n - d = m then ((Nat.choose d (n - d) : ℕ) : ℚ) * (-1 : ℚ) ^ (n - d) else 0) := by
    intro m hm
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
    split_ifs with hcon
    · subst hcon
      rw [smul_eq_mul, mul_one]
    · rw [smul_zero]
  rw [hcc, one_sub_X_pow, map_sum]
  have hsum : (∑ m ∈ Finset.range (d + 1),
      PowerSeries.coeff (n - d) ((((Nat.choose d m : ℕ) : ℚ) * (-1 : ℚ) ^ m) • PowerSeries.X ^ m))
      = ∑ m ∈ Finset.range (d + 1),
        (if n - d = m then ((Nat.choose d (n - d) : ℕ) : ℚ) * (-1 : ℚ) ^ (n - d) else 0) :=
    Finset.sum_congr rfl (fun m hm => hterm m hm)
  rw [hsum, Finset.sum_ite_eq]
  split_ifs with hmem
  · rfl
  · simp only [Finset.mem_range, not_lt] at hmem
    have h0 : Nat.choose d (n - d) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0, Nat.cast_zero, zero_mul]

private lemma B_eq_subst (a b : ℕ → ℚ)
    (h : ∀ n, b n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) * (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) * a j) :
    PowerSeries.mk b = PowerSeries.subst CatF (PowerSeries.mk a) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mk]
  have hsub : PowerSeries.coeff n (PowerSeries.subst CatF (PowerSeries.mk a))
      = ∑ᶠ d, a d • PowerSeries.coeff n (CatF ^ d) := by
    rw [PowerSeries.coeff_subst' CatF_subst]
    simp only [PowerSeries.coeff_mk]
  rw [hsub]
  have hFd : ∀ d, CatF ^ d = PowerSeries.X ^ d * CatQ ^ d := by
    intro d
    change (PowerSeries.X * CatQ) ^ d = _
    rw [mul_pow]
  have hzero : ∀ d, n < d → a d • PowerSeries.coeff n (CatF ^ d) = 0 := by
    intro d hnd
    have h0 : PowerSeries.coeff n (CatF ^ d) = 0 := by
      rw [hFd, PowerSeries.coeff_X_pow_mul']
      rw [ite_eq_right (by omega : ¬ d ≤ n)]
    rw [h0, smul_zero]
  have hsupp : Function.support (fun d => a d • PowerSeries.coeff n (CatF ^ d))
      ⊆ ↑(Finset.range (n + 1)) := by
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hc
    exact Function.mem_support.mp hd (hzero d (by omega))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hb0 : b 0 = a 0 := by
      have h0 := h 0
      simp only [zero_add, Finset.sum_range_one] at h0
      simpa using h0
    rw [hb0]
    simp only [zero_add, Finset.sum_range_one]
    rw [pow_zero, PowerSeries.coeff_one, ite_eq_left rfl, smul_eq_mul, mul_one]
  · have h1 := first_form a b h n hn
    rw [h1]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finset.mem_range] at hd
    have hdn : d ≤ n := by omega
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · simp only [Nat.cast_zero, zero_div, zero_mul, pow_zero, PowerSeries.coeff_one,
        ite_eq_right (show n ≠ 0 by omega), smul_zero]
    · have hcc : PowerSeries.coeff n (CatF ^ d)
          = PowerSeries.coeff (n - d) (CatQ ^ d) := by
        rw [hFd]
        have e : n = (n - d) + d := by omega
        nth_rewrite 1 [e]
        exact PowerSeries.coeff_X_pow_mul _ _ _
      have hcp := Cpow_coeff (n - d) d hdpos
      have eN : d + 2 * (n - d) = 2 * n - d := by omega
      have ec : (((2 * n - d : ℕ)) : ℚ) = 2 * (n : ℚ) - (d : ℚ) := by
        rw [Nat.cast_sub (by omega : d ≤ 2 * n), Nat.cast_mul, Nat.cast_ofNat]
      rw [hcc, hcp, eN, ec, smul_eq_mul]
      ring

private lemma hXsubst : PowerSeries.HasSubst (PowerSeries.X : PowerSeries ℚ) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X

private lemma subst_X_coeff (a : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (PowerSeries.X : PowerSeries ℚ) (PowerSeries.mk a)) = a
        n := by
  rw [PowerSeries.coeff_subst' hXsubst]
  simp only [PowerSeries.coeff_mk]
  have hsupp : Function.support (fun d => a d • PowerSeries.coeff n
      ((PowerSeries.X : PowerSeries ℚ) ^ d))
      ⊆ ↑({n} : Finset ℕ) := by
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_singleton]
    by_contra hc
    exact Function.mem_support.mp hd (by
      have h0 : PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℚ) ^ d) = 0 := by
        rw [PowerSeries.coeff_X_pow n d, ite_eq_right (by omega : ¬ n = d)]
      rw [h0, smul_zero])
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_singleton, PowerSeries.coeff_X_pow n n, ite_eq_left rfl, smul_eq_mul, mul_one]

private lemma short_inv (a b : ℕ → ℚ)
    (h : ∀ n, b n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) * (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) * a j)
    (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1),
      (Nat.choose k (n - k) : ℚ) * (-1 : ℚ) ^ (n - k) * b k := by
  have hB : PowerSeries.mk b = PowerSeries.subst CatF (PowerSeries.mk a) :=
    B_eq_subst a b h
  have hcomp : PowerSeries.subst CatG (PowerSeries.mk b)
      = PowerSeries.subst PowerSeries.X (PowerSeries.mk a) := by
    have e : PowerSeries.subst CatG (PowerSeries.mk b)
        = PowerSeries.subst CatG (PowerSeries.subst CatF (PowerSeries.mk a)) := by
      rw [hB]
    rw [e, PowerSeries.subst_comp_subst_apply CatF_subst CatG_subst, subst_G_F]
  have hA : a n = PowerSeries.coeff n (PowerSeries.subst CatG (PowerSeries.mk b)) := by
    rw [hcomp]
    exact (subst_X_coeff a n).symm
  rw [hA, PowerSeries.coeff_subst' CatG_subst]
  simp only [PowerSeries.coeff_mk]
  have hG : CatG = PowerSeries.X * (1 - PowerSeries.X) := by unfold CatG; ring
  have hzero : ∀ d, n < d → b d • PowerSeries.coeff n (CatG ^ d) = 0 := by
    intro d hnd
    have h0 : PowerSeries.coeff n (CatG ^ d) = 0 := by
      have hGd : CatG ^ d = PowerSeries.X ^ d * (1 - PowerSeries.X) ^ d := by
        rw [hG, mul_pow]
      rw [hGd, PowerSeries.coeff_X_pow_mul']
      rw [ite_eq_right (by omega : ¬ d ≤ n)]
    rw [h0, smul_zero]
  have hsupp : Function.support (fun d => b d • PowerSeries.coeff n (CatG ^ d))
      ⊆ ↑(Finset.range (n + 1)) := by
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hc
    exact Function.mem_support.mp hd (hzero d (by omega))
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_range] at hd
  rw [Gpow_coeff d n (by omega), smul_eq_mul]
  ring

private lemma long_inv (a b : ℕ → ℚ)
    (h : ∀ n, b n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) * (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) * a j)
    (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n / 2 + 1),
      (Nat.choose (n - k) k : ℚ) * (-1 : ℚ) ^ k * b (n - k) := by
  have hshort := short_inv a b h n
  have hrefl : (∑ k ∈ Finset.range (n + 1),
        (Nat.choose k (n - k) : ℚ) * (-1 : ℚ) ^ (n - k) * b k)
      = ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (n + 1 - 1 - k) (n - (n + 1 - 1 - k)) : ℚ) *
          (-1 : ℚ) ^ (n - (n + 1 - 1 - k)) * b (n + 1 - 1 - k) :=
    (Finset.sum_range_reflect _ _).symm
  rw [hshort, hrefl]
  trans ∑ k ∈ Finset.range (n + 1),
    (Nat.choose (n - k) k : ℚ) * (-1 : ℚ) ^ k * b (n - k)
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    have e1 : n + 1 - 1 - k = n - k := by omega
    have e2 : n - (n - k) = k := by omega
    rw [e1, e2]
  · apply (Finset.sum_subset _ _).symm
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro k hk hnk
      simp only [Finset.mem_range] at hk hnk
      have h0 : Nat.choose (n - k) k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]

/-- **Barry's Catalan transform and its inverse.** Let $a, b \colon \mathbb{N} \to \mathbb{Q}$ be
sequences such that, for every $n \ge 0$,
$$b_n = \sum_{j=0}^{n} \sum_{k=0}^{n} \frac{2k+1}{n+k+1} (-1)^{k-j}
\binom{2n}{n-k} \binom{k}{j} a_j.$$
Then for every $n \ge 1$ both
$$b_n = \sum_{k=0}^{n} \frac{k}{2n-k} \binom{2n-k}{n-k} a_k$$
and
$$b_n = \sum_{k=0}^{n} \frac{k}{n} \binom{2n-k-1}{n-k} a_k$$
hold, and for every $n \ge 0$ both
$$a_n = \sum_{k=0}^{\lfloor n/2 \rfloor} (-1)^k \binom{n-k}{k} b_{n-k}$$
and
$$a_n = \sum_{k=0}^{n} (-1)^{n-k} \binom{k}{n-k} b_k$$
hold.

In the hypothesis, the terms with $j > k$ vanish because $\binom{k}{j} = 0$ there.

Proves `Wanted` entry `catalan_transform_pair`.

Source: Paul Barry, "A Catalan Transform and Related Transformations on
Integer Sequences", Journal of Integer Sequences 8 (2005), Article 05.4.5,
proposition lines 302--311,
<https://cs.uwaterloo.ca/journals/JIS/VOL8/Barry/barry84.tex>.
-/
theorem catalan_transform_pair (a b : ℕ → ℚ)
    (h : ∀ n, b n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℚ) + 1) / ((n : ℚ) + (k : ℚ) + 1)) * (-1 : ℚ) ^ (k - j) *
        (Nat.choose (2 * n) (n - k) : ℚ) * (Nat.choose k j : ℚ) * a j) :
    (∀ n, 0 < n → b n = ∑ k ∈ Finset.range (n + 1),
      ((k : ℚ) / (2 * (n : ℚ) - (k : ℚ))) * (Nat.choose (2 * n - k) (n - k) : ℚ) * a k) ∧
    (∀ n, 0 < n → b n = ∑ k ∈ Finset.range (n + 1),
      ((k : ℚ) / (n : ℚ)) * (Nat.choose (2 * n - k - 1) (n - k) : ℚ) * a k) ∧
    (∀ n, a n = ∑ k ∈ Finset.range (n / 2 + 1),
      (Nat.choose (n - k) k : ℚ) * (-1 : ℚ) ^ k * b (n - k)) ∧
    (∀ n, a n = ∑ k ∈ Finset.range (n + 1),
      (Nat.choose k (n - k) : ℚ) * (-1 : ℚ) ^ (n - k) * b k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    exact first_form a b h n hn
  · intro n hn
    exact second_form a b h n hn
  · intro n
    exact long_inv a b h n
  · intro n
    exact short_inv a b h n

end MetaMathlibExt
end
